#!/bin/bash
cd /srv/fv-uint256-we
while [ ! -f build/chain3.done ]; do sleep 30; done
build/snapv5.sh amd64 Dec Fv256/Amd64/Dec.lean decamd-m1 Fv256.Amd64.Dec.correctness Fv256.Amd64.Dec.Witness.nonvacuous
build/snapv5.sh arm64 Dec Fv256/Arm64/Dec.lean decarm-m1 Fv256.Arm64.Dec.correctness Fv256.Arm64.Dec.Witness.nonvacuous
build/snapv5.sh amd64 String Fv256/Amd64/String.lean stramd-m1 Fv256.Amd64.String.correctness Fv256.Amd64.String.Witness.nonvacuous
build/snapv5.sh arm64 String Fv256/Arm64/String.lean strarm-m1 Fv256.Arm64.String.correctness Fv256.Arm64.String.Witness.nonvacuous
echo done > build/chain4.done
