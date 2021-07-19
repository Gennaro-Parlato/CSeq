rounds=$1
unwind=$2
files=sequentialized${1}R${2}U/output_dr_2*
echo "@###########  FAILED  ######" 
grep FAILED $files 
