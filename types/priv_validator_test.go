/*
 *  Copyright 2018 KardiaChain
 *  This file is part of the go-kardia library.
 *
 *  The go-kardia library is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Lesser General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  The go-kardia library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with the go-kardia library. If not, see <http://www.gnu.org/licenses/>.
 */

package types

import (
	"crypto/ecdsa"
	"testing"

	"github.com/kardiachain/go-kardia/lib/crypto"
)

func TestPrivValidatorAccessors(t *testing.T) {
	privValidator, privateKey, publicKey := CreateNewPrivValidator()
	address := privValidator.GetAddress()
	if address != crypto.PubkeyToAddress(publicKey) {
		t.Error("PV GetAddress error")
	}

	if privValidator.GetPubKey() != publicKey || *privValidator.GetPrivKey() != privateKey {
		t.Error("PV Getkeys error")
	}
}

func TestPrivValidatorSignVote(t *testing.T) {
	vote := &Vote{}
	privValidator, _, _ := CreateNewPrivValidator()
	if err := privValidator.SignVote("KAI", vote.ToProto()); err != nil {
		t.Fatal("PV Sign Vote issue", err)
	}
}

func TestPrivValidatorSignProposal(t *testing.T) {
	proposal := NewProposal(1, 2, 3, createBlockIDRandom())
	privValidator, _, _ := CreateNewPrivValidator()
	if err := privValidator.SignProposal("KAI", proposal.ToProto()); err != nil {
		t.Fatal("PV Sign Proposal issue", err)
	}
}

func CreateNewPrivValidator() (*DefaultPrivValidator, ecdsa.PrivateKey, ecdsa.PublicKey) {
	priv, _ := crypto.GenerateKey()
	return NewDefaultPrivValidator(priv), *priv, priv.PublicKey
}
