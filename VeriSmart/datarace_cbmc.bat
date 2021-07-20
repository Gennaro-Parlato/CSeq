sourcedir=/home/salvatore/ShadowMemory/svcomp2020-concurrency-benchmarks/
result=${sourcedir}resultscbmc${1}R${2}U.out
seqdir=${sourcedir}sequentialized${1}R${2}U/

if [ -f $result ]; then
    rm $result
fi

if [ ! -d $seqdir ]; then
    mkdir $seqdir
fi

for file in ${seqdir}*
do
  if [[ $file == *.c ]];
  then
     noExtFile=${file::-2}
     prefix="output"
     suffix=${noExtFile#${seqdir}}
     echo "./cbmc-SM $file --unwind 1 --no-unwinding-assertions --stop-on-fail"
     output=${seqdir}$prefix$suffix
     (time  timeout -k 10 900 ./cbmc-SM $file --unwind 1 --no-unwinding-assertions --stop-on-fail) > $output  2>&1
     (cat "$output" | grep '^user\|^[[:digit:]]\{1,10\} variables\|^Runtime decision \|^CBMC \|^Parsing\|^VERIFICATION') >> $result
     echo "" >> $result
  fi
done
