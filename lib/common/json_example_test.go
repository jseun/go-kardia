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

package common

import (
	"encoding/json"
	"fmt"
)

type MyType [5]byte

func (v *MyType) UnmarshalText(input []byte) error {
	return UnmarshalFixedText("MyType", input, v[:])
}

func (v MyType) String() string {
	return Bytes(v[:]).String()
}

func ExampleUnmarshalFixedText() {
	var v1, v2 MyType
	fmt.Println("v1 error:", json.Unmarshal([]byte(`"0x01"`), &v1))
	fmt.Println("v2 error:", json.Unmarshal([]byte(`"0x0101010101"`), &v2))
	fmt.Println("v2:", v2)
	// Output:
	// v1 error: hex string has length 2, want 10 for MyType
	// v2 error: <nil>
	// v2: 0x0101010101
}
