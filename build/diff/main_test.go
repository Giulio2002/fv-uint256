package main
import ("testing";"math/big";"github.com/holiman/uint256")
func TestF(t *testing.T){
 x:=new(big.Int).Add(new(big.Int).Lsh(big.NewInt(1),64),big.NewInt(4095))
 u,_:=uint256.FromBig(x)
 f,_:=new(big.Float).SetInt(x).Float64()
 t.Logf("x=2^64+4095 uint256=%v (bits %x) big=%v (bits %x)", u.Float64(), u.Float64(), f, f)
 // SDiv INT_MIN / -1, SMod
 min:=new(uint256.Int).Lsh(uint256.NewInt(1),255)
 m1:=new(uint256.Int).SetAllOne()
 var z uint256.Int
 t.Logf("SDiv(INT_MIN,-1)=%s SMod(INT_MIN,-1)=%s SDiv(5,0)=%s SMod(5,0)=%s", z.SDiv(min,m1).Hex(), new(uint256.Int).SMod(min,m1).Hex(), new(uint256.Int).SDiv(uint256.NewInt(5),new(uint256.Int)).Hex(), new(uint256.Int).SMod(uint256.NewInt(5),new(uint256.Int)).Hex())
}
