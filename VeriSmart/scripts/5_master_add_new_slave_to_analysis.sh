
#echo "$1 $2" | sudo tee -a /etc/hosts
#echo "$1 slots=$3" | sudo tee -a /home/aldo/CSeq-master/VeriSmart/nodes
#echo "65536" | sudo su - aldo -c "ssh-keyscan $2 > .ssh/known_hosts"
#sudo sshpass -p '65536' ssh-copy-id -f -o StrictHostKeyChecking=no -i /home/aldo/.ssh/id_rsa aldo@$2

# add new slave to master's hosts file
echo "slave6 10.0.0.182" | sudo tee -a /etc/hosts

# add new slave to verismart MPI communicator
echo "slave6 slots=1" | sudo tee -a /home/aldo/CSeq-master/VeriSmart/nodes

# add new slave as a new known host for master
echo "65536" | sudo su - aldo -c "ssh-keyscan slave6 > .ssh/known_hosts"

# master gives access to itself without password to the new slave
# master sends its public key to the new slave
sudo sshpass -p '65536' ssh-copy-id -f -o StrictHostKeyChecking=no -i /home/aldo/.ssh/id_rsa aldo@slave6
