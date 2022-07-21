echo "65536" | sudo su - aldo -c "ssh-keygen -t rsa -f /home/aldo/.ssh/id_rsa -q -P "65536""

echo "65536" | sudo su - aldo -c "ssh-keyscan master > .ssh/known_hosts"

echo "65536" | sudo su - aldo -c "sshpass -p "65536" ssh-copy-id aldo@master"

echo "65536" | sudo su - aldo -c "mkdir CSeq-master"