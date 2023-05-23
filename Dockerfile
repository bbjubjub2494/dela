# Specifies a parent image
FROM golang:1.20

RUN apt-get update
RUN apt-get install -y tmux
 
# Creates an app directory to hold your app’s source code
WORKDIR /app
 
# Copies everything from your root directory into /app
COPY ./ /app/
 
# Installs Go dependencies
RUN go mod download
