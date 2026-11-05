#!/usr/bin/env bash
sed -e 's/IDiv/IMod/g; s/DivSum.div_summary/ModSum.mod_summary/; s/Amd64.DivSum/Amd64.ModSum/; s/divSpec/modSpec/g; s/0x190/0x1b0/g; s/0x1e8/0x208/g; s/0x1e0/0x200/g' \
  -e 's/`z.Div(z, x)`: "Div sets z to the quotient x\/y for returns z. If y == 0, z is set to 0."/`z.Mod(z, x)`: "Mod sets z to the modulus x%y for y != 0. If y == 0, z is set to 0 (OBS: differs from the big.Int)."/' \
  -e 's/z \/ x/z % x/g; s/`Div`/`Mod`/g' /srv/fv-uint256-wd/lean/Fv256/Amd64/IDiv.lean > /srv/fv-uint256-wd/lean/Fv256/Amd64/IMod.lean
