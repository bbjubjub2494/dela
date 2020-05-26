package main

import (
	"fmt"
	"go/parser"
	"go/token"
	"io/ioutil"
	"log"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"time"

	"github.com/urfave/cli/v2"
	"golang.org/x/xerrors"
	"gopkg.in/yaml.v2"
)

/*
	This package provides a utility CLI to generate the dependency graph of each
	package inside a module. You can get the explanations on how to use it with
	`go build && ./depgraph help`.
*/

type config struct {
	Modname    string   `yaml:"modname"`
	Includes   []string `yaml:"includes"`
	Excludes   []string `yaml:"excludes"`
	Interfaces []string `yaml:"interfaces"`
}

func main() {

	app := &cli.App{
		Name:      "depgraph",
		Usage:     "generate a dot graph",
		UsageText: "./depgraph [--config | --modname ] source ",
		Description: `This utility will recursively parse a folder and extract 
for each package that it finds the list of dependencies it uses to generate a
graphviz representation.
Since there might be a lot of dependencies, one can provide a yaml config file
in order to scope the parsing. The config format is the following:

modname: MODULE_NAME
includes:
	- go.dedis.ch/fabric/*
	- ...
excludes:
	- go.dedis.ch/fabric/encoding*
	- ...
interfaces:
	- blockchain
	- ...

"includes" and "excludes" are two lists of regular expressions.

If "includes" is empty then everything is included. Otherwise, the program only
keeps the package AND dependencies that are specified in the includes list.

Each pacakge AND dependency is checked against the "excludes" list and discarded
if it matches any of the elements.

"interfaces" is used to mark specific packages that should be displayed
differently. In this case thoses pacakges will be outlined by a green
background.

Examples:

./depgrah --modname "go.dedis.ch/fabric" -o graph.dot -F ./
./depgrah --config internal/depgraph/config.yml -o graph.dot -F ./

The following commands can be used to generate a visual representation from the
output of depgraph using DOT:

dot -Gdpi=300 -Tpng graph.dot -o graph.png
dot -Gdpi=300 -Tpng graph.dot -o graph.png -Gsplines=ortho`,
		Flags: []cli.Flag{
			&cli.StringFlag{
				Name:    "config",
				Aliases: []string{"c"},
				Usage:   "the path to a yaml config file",
			},
			&cli.StringFlag{
				Name: "modname",
				Usage: "the module name, convenient if one doesn't want to " +
					"provide a config file. Overwrites value from the config " +
					"file if provided.",
			},
			&cli.StringFlag{
				Name:    "out",
				Aliases: []string{"o"},
				Usage:   "if provided will save the result to the specified file",
			},
			&cli.BoolFlag{
				Name:    "force",
				Aliases: []string{"F"},
				Usage:   "overwrite the output file",
			},
		},
		Action: run,
	}

	err := app.Run(os.Args)
	if err != nil {
		log.Fatal(err)
	}
}

func run(c *cli.Context) error {
	if c.NArg() == 0 {
		return xerrors.Errorf("please provide the folder path")
	}

	searchDir := c.Args().First()
	if searchDir == "" {
		return xerrors.Errorf("please provide a root with '--root'")
	}

	config := config{}
	configPath := c.String("config")
	if configPath != "" {
		configBuf, err := ioutil.ReadFile(configPath)
		if err != nil {
			log.Fatal(err)
		}

		err = yaml.Unmarshal([]byte(configBuf), &config)
		if err != nil {
			log.Fatalf("error: %v", err)
		}

		config.Modname = config.Modname + "/"
	}

	if c.String("modname") != "" {
		// we add a "/" to build the full package name. If the module name is
		// mod.ch/module, then a package 'pancake' inside it should be
		// mod.ch/module/pancake, but the parsing will only extract 'pancake'.
		config.Modname = c.String("modname") + "/"
	}

	fset := token.NewFileSet()
	out := os.Stdout

	if c.String("out") != "" {
		_, err := os.Stat(c.String("out"))
		if !os.IsNotExist(err) && !c.Bool("force") {
			return xerrors.Errorf("file '%s' already exist, use '-F' to "+
				"overwrite", c.String("out"))
		}

		out, err = os.Create(c.String("out"))
		if err != nil {
			return xerrors.Errorf("failed to create output file: %v", err)
		}
	}

	// We built a bag of interfaces with a map, the bool value is meaningless.
	interfaces := map[string]bool{}
	for _, it := range config.Interfaces {
		interfaces[it] = true
	}

	// links will contain for every package a bag of dependencies. The bag is
	// done with a dummy map.
	links := make(map[string]map[string]bool)

	// parseFile will be called recusively on each file and folder
	parseFile := func(path string, f os.FileInfo, err error) error {
		if err != nil {
			return xerrors.Errorf("got an error while walking: %v", err)
		}

		// we exclude the dir, non-go files and test files
		if f.IsDir() || !strings.HasSuffix(f.Name(), ".go") ||
			strings.HasSuffix(f.Name(), "_test.go") {

			return nil
		}

		astFile, err := parser.ParseFile(fset, path, nil, parser.ImportsOnly)
		if err != nil {
			return xerrors.Errorf("failed to parse file: %v", err)
		}

		path = filepath.Dir(path)
		// This is the full package path. From "mino" we want
		// "go.dedis.ch/fabric/mino"
		packagePath := config.Modname + path

		if !isIncluded(packagePath, config.Includes) ||
			isExcluded(packagePath, config.Excludes) {
			return nil
		}

		for _, s := range astFile.Imports {
			// because an import path is always surrounded with "" we remove
			// them
			importPath := s.Path.Value[1 : len(s.Path.Value)-1]

			if !isIncluded(importPath, config.Includes) ||
				isExcluded(importPath, config.Excludes) {

				continue
			}

			// in the case the package imports a package from the same module,
			// we want to keep only the "relative" name. From
			// "go.dedis.ch/fabric/mino/minogrpc" we want only "mino/minogrpc".
			importPath = strings.TrimPrefix(importPath, config.Modname)

			if links[packagePath[len(config.Modname):]] == nil {
				links[packagePath[len(config.Modname):]] = make(map[string]bool)
			}

			// add the dependency to the bag
			links[packagePath[len(config.Modname):]][importPath] = true
		}

		return nil
	}

	err := filepath.Walk(searchDir, parseFile)
	if err != nil {
		return xerrors.Errorf("failed to parse folder: %v", err)
	}

	// a bag of nodes, used to keep track of every node added so that we can
	// later on outline the interfaces.
	nodesList := make(map[string]bool)

	fmt.Fprintf(out, "strict digraph {\n")
	fmt.Fprintf(out, "labelloc=\"t\";\n")
	fmt.Fprintf(out, "label = <Modules dependencies of Dela "+
		"<font point-size='10'><br/>(generated %s)</font>>;\n",
		time.Now().Format("2 Jan 06 - 15:04:05"))
	fmt.Fprintf(out, "graph [fontname = \"helvetica\"];\n")
	fmt.Fprintf(out, "graph [fontname = \"helvetica\"];\n")
	fmt.Fprintf(out, "node [fontname = \"helvetica\"];\n")
	fmt.Fprintf(out, "edge [fontname = \"helvetica\"];\n")
	fmt.Fprintf(out, "node [shape=box,style=rounded];\n")
	// To have (more or less) deterministric result
	fmt.Fprintf(out, "start=0;\n")
	fmt.Fprintf(out, "ratio = fill;\n")
	fmt.Fprintf(out, "rankdir=\"LR\";\n")

	for pkg, depsBag := range links {
		nodesList[pkg] = true

		for dep := range depsBag {
			nodesList[dep] = true
			fmt.Fprintf(out, "\"%v\" -> \"%v\" [minlen=1];\n", pkg, dep)
		}
	}

	// outlines the interface nodes
	for k := range nodesList {
		_, found := interfaces[k]
		if found {
			fmt.Fprintf(out, "\"%s\" [style=filled fillcolor=mediumspringgreen];\n", k)
		}
	}

	fmt.Fprintf(out, "}\n")

	return nil

}

func isIncluded(path string, includes []string) bool {
	if len(includes) == 0 {
		return true
	}

	return matchSlice(path, includes)
}

func isExcluded(path string, excludes []string) bool {
	return matchSlice(path, excludes)
}

func matchSlice(el string, slice []string) bool {
	for _, e := range slice {
		reg := regexp.MustCompile(e)

		ok := reg.MatchString(el)
		if ok {
			return true
		}
	}

	return false
}
