rounds=$1
unwind=$2
files=sequentialized${1}R${2}U/output_csdr_*
echo -ne "FAILED = " 
grep FAILED $files | wc -l  
echo -ne "SUCCESSFUL = " 
grep SUCCESSFUL $files | wc -l
echo -ne "Invariant check failed = " 
grep "Invariant check failed" $files | wc -l
echo -ne "PARSING ERROR = " 
grep "PARSING ERROR" $files | wc -l
echo -ne "CONVERSION ERROR = " 
grep "CONVERSION ERROR" $files | wc -l
echo -ne "Timeout = " 
grep "real	60" $files | wc -l
echo -ne "SAT out of memory = " 
grep "SAT checker ran out of memory" $files | wc -l
echo -ne "TOTAL = " 
ls $files | wc -l
