import sys
# tries.py "simp-set" : bounds for z,x,y (whichever in scope) then simp only [set]; omega
ps=['z','x','y']
parts=[f"(try have := Util.readLE8_lt s.mem ({p}.toNat {o}))" for p in ps for o in ['','+ 8','+ 16','+ 24']]
print('; '.join(parts)+"; "+sys.argv[1])
