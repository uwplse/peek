import sys

with open(sys.argv[1],'r') as results:
    for res in results.readlines():
        if not res[0].isdigit():
            s = res.split(":")
            name = s[0]
            t = s[1]
            x = t.split("use")
            t = x[0]
            print name + "," + t
            


        
