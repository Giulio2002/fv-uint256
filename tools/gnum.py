import ast, random
M = 2 ** 64
def conv(e):
    e = e.replace('/', '//')
    while 'decide' in e:
        i = e.index('(decide (0 <'); d = 0
        for j in range(i, len(e)):
            if e[j] == '(': d += 1
            elif e[j] == ')':
                d -= 1
                if d == 0: break
        X = e[i:j + 1][len('(decide (0 < '):-2]; k = j + 1
        e = e[:i] + 'D(%s)' % X + e[k + 6:]
    e = e.replace('18446744073709551615#64', '(2**64-1)')
    return e
D = lambda x: 1 if x > 0 else 0
def run(chain, env):
    eqs = ast.literal_eval(open('/srv/fv-uint256-wBm/lean/Fv256/Amd64/RecipG/c_%s.eqs' % chain).read())
    for n, e in eqs: env[n] = eval(conv(e), {'D': D}, env)
    return env
