import sys
op=sys.argv[1]
b=' '.join(['(Util.readLE8_lt _ _)']*8)
print(f"simp only [Spec.{op}]; exact Util.lt_ite _ _ _ _ _ _ _ _ {b}")
