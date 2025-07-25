package pod

import (
	"crypto/sha256"
	"errors"
	"fmt"
	"math/big"
	"regexp"
	"sort"

	"github.com/iden3/go-iden3-crypto/v2/constants"
	"github.com/iden3/go-iden3-crypto/v2/poseidon"
)

// Private keys are 32 bytes (any arbitrary bytes), represented as Base64 or
// hexadecimal
//
// This regex matches any supported format, with match groups usable to
// determine the format, in the order above.
var PrivateKeyRegex = regexp.MustCompile(`^(?:([A-Za-z0-9+/]{43}=?)|([0-9A-Fa-f]{64}))$`)

// Public keys are 32 bytes (a packed elliptic curve point), represented as
// Base64 or hexadecimal.  Base64 padding is optional.
//
// This regex matches any supported format, with match groups usable to
// determine the format, in the order above.
var PublicKeyRegex = regexp.MustCompile(`^(?:([A-Za-z0-9+/]{43}=?)|([0-9A-Fa-f]{64}))$`)

// Signatures are 64 bytes (one packed elliptic curve point, one scalar),
// represented as Base64 or hexadecimal.  Base64 padding is optional.
//
// This regex matches any supported format, with match groups usable to
// determine the format, in the order above.
var SignatureRegex = regexp.MustCompile(`^(?:([A-Za-z0-9+/]{86}(?:==)?)|([0-9A-Fa-f]{128}))$`)

func hashString(s string) *big.Int {
	return hashBytes([]byte(s))
}

// hashBytes hashes the byte slice with SHA-256, then interprets
// the first 31 bytes of that digest as a big-endian integer.
func hashBytes(data []byte) *big.Int {
	hash := sha256.Sum256(data)
	first31 := hash[:31]
	x := new(big.Int).SetBytes(first31)
	return x
}

func fieldSafeInt64(val int64) *big.Int {
	x := big.NewInt(val)
	x.Mod(x, constants.Q)
	return x
}

func computeContentID(data PodEntries) (*big.Int, error) {
	if err := data.Check(); err != nil {
		return nil, err
	}

	keys := make([]string, 0, len(data))
	for k := range data {
		keys = append(keys, k)
	}
	sort.Strings(keys)

	var allHashes []*big.Int
	for _, k := range keys {
		kh := hashString(k)
		allHashes = append(allHashes, kh)

		vh, err := data[k].Hash()
		if err != nil {
			return nil, fmt.Errorf("error when hashing pod value: %w", err)
		}
		allHashes = append(allHashes, vh)
	}

	root, err := leanPoseidonIMT(allHashes)
	if err != nil {
		return nil, fmt.Errorf("error when computing poseidon IMT: %w", err)
	}
	return root, nil
}

func leanPoseidonIMT(inputs []*big.Int) (*big.Int, error) {
	if len(inputs) == 0 {
		return nil, errors.New("at least one input is required")
	}

	items := make([]*big.Int, len(inputs))
	copy(items, inputs)

	for len(items) > 1 {
		var newItems []*big.Int
		for i := 0; i < len(items); i += 2 {
			if i+1 < len(items) {
				h, err := poseidon.Hash([]*big.Int{items[i], items[i+1]})
				if err != nil {
					return nil, fmt.Errorf("error hashing chunk: %w", err)
				}
				newItems = append(newItems, h)
			} else {
				newItems = append(newItems, items[i])
			}
		}
		items = newItems
	}
	return items[0], nil
}
