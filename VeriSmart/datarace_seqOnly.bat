sourcedir=/home/salvatore/ShadowMemory/svcomp2020-concurrency-benchmarks/
result=${sourcedir}results${1}R${2}U.out
seqdir=${sourcedir}sequentialized${1}R${2}U/
outdir=${sourcedir}output/

if [ -f $result ]; then
    rm $result
fi

if [ ! -d $seqdir ]; then
    mkdir $seqdir
fi

if [ ! -d $outdir ]; then
    mkdir $outdir
fi

parsed=0
for d in ${sourcedir}* 
do
   if [ -d $d ];  then
      for file in ${d}/*
      do
        if [[ $file == *.i ]]; then
           parsed=$((parsed+1))
           echo $parsed >> $result
           echo "./lazycseq.py -i $file --rounds $1 --unwind $2 --seq --dr --debug" >> $result
           echo $parsed
           echo $file
           noExtFile=${file::-2}
           suffix=${noExtFile#${d}/}
           output=${outdir}output$suffix
           (./lazycseq.py -i $file --rounds $1 --unwind $2 --seq --dr --debug) > $output 2>&1 
           (cat "$output" | grep '^[[:digit:]]\{1,4\}\s*$\|Error\|Segmentation\|error\|Aborted\|dr_cex') >> $result
           echo " " >> $result
           outfile=${d}/_csdr_${suffix}.c
           newoutfile=${seqdir}_csdr_${suffix}.c
           mv $outfile $newoutfile 
        fi
      done
   fi
done
