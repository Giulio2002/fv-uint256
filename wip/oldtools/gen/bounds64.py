import sys
op=sys.argv[1]; ps=sys.argv[2:]
parts=[f"have := Util.readLE8_lt s.mem ({p}.toNat {o})" for p in ps for o in ['','+ 8','+ 16','+ 24']]
print('; '.join(parts)+f"; simp only [Spec.{op}]; (repeat janus_decide_split); all_goals omega")
