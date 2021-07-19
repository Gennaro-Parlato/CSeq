rounds=$1
unwind=$2
files=sequentialized${1}R${2}U/output_csdr_*
echo "@###########  FAILED  ######" 
grep FAILED $files 
echo ""
echo "@############  SUCCESSFUL  ########" 
grep SUCCESSFUL $files 
echo "@###########  Invalid check failed  #########" 
grep "Invariant check failed" $files 
echo "@#############  PARSING ERROR  ###########" 
grep "PARSING ERROR" $files 
echo "@############  CONVERSION ERROR  ###########" 
grep "CONVERSION ERROR" $files 
echo "@############  Timeout  ############" 
grep "real	60" $files 
echo "@#########   SAT out of memory  ##############" 
grep "SAT checker ran out of memory" $files 
echo -ne "TOTAL = " 
ls $files | wc -l
