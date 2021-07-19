sourcedir=/home/salvatore/ShadowMemory/svcomp2020-concurrency-benchmarks/
result=${sourcedir}diffcbmc${1}R${2}U.out
seqdir=${sourcedir}sequentialized${1}R${2}U/
tmp1=${sourcedir}tmp1.out
tmp2=${sourcedir}tmp2.out

if [ -f $result ]; then
    rm $result
fi

for file in ${seqdir}*
do
  if [[ $file == *.c ]];
  then
     noExtFile=${file::-2}
     prefix1="4673_output"
     prefix2="new_output"
     suffix=${noExtFile#${seqdir}}
     output1=${seqdir}$prefix1$suffix
     output2=${seqdir}$prefix2$suffix
     (cat "$output1" | grep '^Parsing') >> $result
     (cat "$output1" | grep '^user\|^[[:digit:]]\{1,10\} variables\|^Runtime decision \|^VERIFICATION') > $tmp1
     (cat "$output2" | grep '^user\|^[[:digit:]]\{1,10\} variables\|^Runtime decision \|^VERIFICATION') > $tmp2
     (diff "$tmp1" "$tmp2") >> $result
     echo "" >> $result
  fi
done

if [ -f $tmp1 ]; then
    rm $tmp1
fi
if [ -f $tmp2 ]; then
    rm $tmp2
fi
