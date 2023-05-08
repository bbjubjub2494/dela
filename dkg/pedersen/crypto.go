package pedersen

import (
	"crypto/sha256"
	"go.dedis.ch/dela/dkg/pedersen/types"
	"go.dedis.ch/kyber/v3"
	"golang.org/x/xerrors"
	"go.dedis.ch/kyber/v3/pairing"
	"go.dedis.ch/kyber/v3/share"
	"go.dedis.ch/kyber/v3/sign/tbls"
)

// A lot of this code deals with low-level crypto to verify DKG proofs.
// TODO: move low-level DKG proof verification functions to Kyber. (#241)

// checkDecryptionProof verifies the decryption proof.
//
// See https://arxiv.org/pdf/2205.08529.pdf / section 5.4 Protocol / step 3
func checkDecryptionProof(sp types.ShareAndProof, K kyber.Point) error {

	tmp1 := suite.Point().Mul(sp.Fi, K)
	tmp2 := suite.Point().Mul(sp.Ei, sp.Ui)
	UHat := suite.Point().Sub(tmp1, tmp2)

	tmp1 = suite.Point().Mul(sp.Fi, nil)
	tmp2 = suite.Point().Mul(sp.Ei, sp.Hi)
	HHat := suite.Point().Sub(tmp1, tmp2)

	hash := sha256.New()
	sp.Ui.MarshalTo(hash)
	UHat.MarshalTo(hash)
	HHat.MarshalTo(hash)
	tmp := suite.Scalar().SetBytes(hash.Sum(nil))

	if !tmp.Equal(sp.Ei) {
		return xerrors.Errorf("hash is not valid: %x != %x", sp.Ei, tmp)
	}

	return nil
}

// checkEncryptionProof verifies the encryption proofs.
//
// See https://arxiv.org/pdf/2205.08529.pdf / section 5.4 Protocol / step 3
func checkEncryptionProof(cp types.Ciphertext) error {

	tmp1 := suite.Point().Mul(cp.F, nil)
	tmp2 := suite.Point().Mul(cp.E, cp.K)
	w := suite.Point().Sub(tmp1, tmp2)

	tmp1 = suite.Point().Mul(cp.F, cp.GBar)
	tmp2 = suite.Point().Mul(cp.E, cp.UBar)
	wBar := suite.Point().Sub(tmp1, tmp2)

	hash := sha256.New()
	cp.C.MarshalTo(hash)
	cp.K.MarshalTo(hash)
	cp.UBar.MarshalTo(hash)
	w.MarshalTo(hash)
	wBar.MarshalTo(hash)

	tmp := suite.Scalar().SetBytes(hash.Sum(nil))
	if !tmp.Equal(cp.E) {
		return xerrors.Errorf("hash not valid: %x != %x", cp.E, tmp)
	}

	return nil
}

// verifiableDecryption generates the decryption shares as well as the
// decryption proof.
//
// See https://arxiv.org/pdf/2205.08529.pdf / section 5.4 Protocol / step 3
func verifiableDecryption(ct types.Ciphertext, V kyber.Scalar, I int) (*types.ShareAndProof, error) {
	err := checkEncryptionProof(ct)
	if err != nil {
		return nil, xerrors.Errorf("failed to check proof: %v", err)
	}

	ui := suite.Point().Mul(V, ct.K)

	// share of this party, needed for decrypting
	partial := suite.Point().Sub(ct.C, ui)

	si := suite.Scalar().Pick(suite.RandomStream())
	UHat := suite.Point().Mul(si, ct.K)
	HHat := suite.Point().Mul(si, nil)

	hash := sha256.New()
	ui.MarshalTo(hash)
	UHat.MarshalTo(hash)
	HHat.MarshalTo(hash)
	Ei := suite.Scalar().SetBytes(hash.Sum(nil))

	Fi := suite.Scalar().Add(si, suite.Scalar().Mul(Ei, V))
	Hi := suite.Point().Mul(V, nil)

	sp := types.ShareAndProof{
		V:  partial,
		I:  int64(I),
		Ui: ui,
		Ei: Ei,
		Fi: Fi,
		Hi: Hi,
	}

	return &sp, nil
}


// NOTE: this is from kyber but s/G1/G2/g
// Verify checks the given BLS signature S on the message m using the public
// key X by verifying that the equality e(H(m), X) == e(H(m), x*B2) ==
// e(x*H(m), B2) == e(S, B2) holds where e is the pairing operation and B2 is
// the base point from curve G2.
func blsVerify(suite pairing.Suite, X kyber.Point, msg, sig []byte) error {
	HM := hashToPoint(suite, msg)
	left := suite.Pair(X, HM)
	s := suite.G2().Point()
	if err := s.UnmarshalBinary(sig); err != nil {
		return err
	}
	right := suite.Pair(s, suite.G1().Point().Base())
	if !left.Equal(right) {
		return xerrors.New("bls: invalid signature")
	}
	return nil
}


// hashToPoint hashes a message to a point on curve G1. XXX: This should be replaced
// eventually by a proper hash-to-point mapping like Elligator.
func hashToPoint(suite pairing.Suite, msg []byte) kyber.Point {
	h := suite.Hash()
	h.Write(msg)
	x := suite.G2().Scalar().SetBytes(h.Sum(nil))
	return suite.G2().Point().Mul(x, nil)
}


// Verify checks the given threshold BLS signature Si on the message m using
// the public key share Xi that is associated to the secret key share xi. This
// public key share Xi can be computed by evaluating the public sharing
// polynonmial at the share's index i.
func tblsVerify(suite pairing.Suite, public *share.PubPoly, msg, sig []byte) error {
	s := tbls.SigShare(sig)
	i, err := s.Index()
	if err != nil {
		return err
	}
	return blsVerify(suite, public.Eval(i).V, msg, s.Value())
}


// NOTE: this is from kyber but s/G1/G2/g
// Recover reconstructs the full BLS signature S = x * H(m) from a threshold t
// of signature shares Si using Lagrange interpolation. The full signature S
// can be verified through the regular BLS verification routine using the
// shared public key X. The shared public key can be computed by evaluating the
// public sharing polynomial at index 0.
func tblsRecover(suite pairing.Suite, public *share.PubPoly, msg []byte, sigs [][]byte, t, n int) ([]byte, error) {
	pubShares := make([]*share.PubShare, 0)
	for _, sig := range sigs {
		s := tbls.SigShare(sig)
		i, err := s.Index()
		if err != nil {
			return nil, err
		}
		if err = blsVerify(suite, public.Eval(i).V, msg, s.Value()); err != nil {
			return nil, err
		}
		point := suite.G2().Point()
		if err := point.UnmarshalBinary(s.Value()); err != nil {
			return nil, err
		}
		pubShares = append(pubShares, &share.PubShare{I: i, V: point})
		if len(pubShares) >= t {
			break
		}
	}
	commit, err := share.RecoverCommit(suite.G2(), pubShares, t, n)
	if err != nil {
		return nil, err
	}
	sig, err := commit.MarshalBinary()
	if err != nil {
		return nil, err
	}
	return sig, nil
}
