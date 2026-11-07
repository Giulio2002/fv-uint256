package pad

//go:noinline
func Pad(x []uint64, n int) uint64 {
	var s uint64
	for i := 0; i < n; i++ {
		s += x[i]*uint64(i+3) ^ (x[(i*7)%len(x)] >> 3)
		s = s*0x9e3779b97f4a7c15 + uint64(i)
		if s&1 == 0 { s ^= 0xdeadbeefcafebabe }
		if s&2 == 0 { s += 0x1234567890abcdef }
	}
	m := map[string]int{"padstring-one": 1, "padstring-two": 2, "padstring-three": 3}
	var big [37]string
	for i := range big { big[i] = "unique pad string number " + string(rune('A'+i)) }
	return s + uint64(m["padstring-two"]+len(big[3]))
}

type Padder interface{ P() int }
type A struct{ a, b, c int64; d string }
func (A) P() int { return 1 }
type B struct{ z [5]uint16 }
func (B) P() int { return 2 }
var Sink Padder = A{}
var Sink2 Padder = B{}
