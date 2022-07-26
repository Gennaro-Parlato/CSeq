# generate private / public key for authentication through ssh
echo "65536" | sudo su - aldo -c "ssh-keygen -t rsa -f /home/aldo/.ssh/id_rsa -q -P '65536'"

for slave in slave1 slave2 slave3 slave4
    do
        # instances on which must be enabled the passwordless communication must be added to the known hosts list
        echo "65536" | sudo su - aldo -c "ssh-keyscan $slave > .ssh/known_hosts"
        # master gives its public key to slaves such that slaves can access to master without authentication
        sudo sshpass -p '65536' ssh-copy-id -f -o StrictHostKeyChecking=no -i /home/aldo/.ssh/id_rsa aldo@$slave
    done
