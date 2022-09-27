eval `ssh-agent -s`
ssh-add
#sshpass -p "65536" ssh-add
python3 ./verismart.py $@
