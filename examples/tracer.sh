#! /bin/sh

# Pass the trace file from rWasm into this file to get convenient gdb-based tracer

grep 'func' "$1" | cut -c 7- | sed 's/]//' | grep -v returned | grep -v IMPORTED | grep -v EXPORTED | sed 's/(/ (/' | awk '{print $1 " " $2}' > "$1.rwasm-calltrace"

sort -nu "$1.rwasm-calltrace" | awk '{print "b func_" $1 "\ncommand\nsilent\npython print(\"" $1 " " $2  "\")\ncontinue\nend\n"}' > "$1.calltrace-vwasm.gdb"
