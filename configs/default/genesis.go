// Package default
package _default

import (
	typesCfg "github.com/kardiachain/go-kardiamain/configs/types"
)

// Genesis configuration
var (
	genesisAddresses = []string{
		"0xc1fe56E3F58D3244F606306611a5d10c8333f1f6",
		"0x7cefC13B6E2aedEeDFB7Cb6c32457240746BAEe5",
		"0xfF3dac4f04dDbD24dE5D6039F90596F0a8bb08fd",
		"0x071E8F5ddddd9f2D4B4Bdf8Fc970DFe8d9871c28",
		"0x94FD535AAB6C01302147Be7819D07817647f7B63",
		"0xa8073C95521a6Db54f4b5ca31a04773B093e9274",
		"0xe94517a4f6f45e80CbAaFfBb0b845F4c0FDD7547",
		"0xBA30505351c17F4c818d94a990eDeD95e166474b",
		"0x212a83C0D7Db5C526303f873D9CeaA32382b55D0",
		"0x8dB7cF1823fcfa6e9E2063F983b3B96A48EEd5a4",
		"0x66BAB3F68Ff0822B7bA568a58A5CB619C4825Ce5",
	}
	genesisAmount = "1000000000000000000000000000"
)

var genesis = &typesCfg.Genesis{
	Addresses:     GenesisAddresses(),
	GenesisAmount: GenesisAmount(),
	Contracts:     Contracts(),
	Validators:    Validators(),
}

func GenesisAddresses() []string {
	return genesisAddresses
}

func GenesisAmount() string {
	return genesisAmount
}

func Genesis() *typesCfg.Genesis {
	return genesis
}
