import sys

peek_agg = {}
nopeek_agg = {}
handtuned_agg = {}
# gcc_agg = {}
# clang_agg = {}

def get_res(l):
    x=l.split(",")
    name=x[0]
    value=float(x[1].split("\n")[0])
    return (name,value)

def get_agg(ls,agg):
    for l in ls:
        (name,value) = get_res(l)
        if (name in agg):
            agg[name] += [value]
        else:
            agg[name] = [value]
        

with open(sys.argv[1],'r') as peek_results:
    with open(sys.argv[2],'r') as nopeek_results:
        with open(sys.argv[3],'r') as handtuned_results:
        # with open(sys.argv[3],'r') as gcc_results:
        #     with open(sys.argv[4],'r') as clang_results:
                get_agg(peek_results.readlines(),peek_agg)
                get_agg(nopeek_results.readlines(),nopeek_agg)
                get_agg(handtuned_results.readlines(),handtuned_agg)
                # get_agg(gcc_results.readlines(),gcc_agg)
                # get_agg(clang_results.readlines(),clang_agg)

def get_avg_err(l):
    if (l == []):
        return "-"
    low = l[0]
    hi = l[0]
    s = 0
    count = 0
    for x in l:
        if x < low:
            low = x
        if x > hi:
            hi = x
            
        s += x
        count += 1
    avg = s/count
    err_low = avg - low
    err_hi = hi - avg
    err = max(err_low,err_hi)
    return str(avg) + " +/- " + str(err)
        
print "benchmark,compcert+peek,compcert,hand-tuned" #,gcc,llvm
for name in peek_agg:
    print name + "," + get_avg_err(peek_agg[name]) + "," + get_avg_err(nopeek_agg[name]) + "," + get_avg_err(handtuned_agg[name]) # + "," + get_avg_err(gcc_agg[name]) + "," + get_avg_err(clang_agg[name])
    
