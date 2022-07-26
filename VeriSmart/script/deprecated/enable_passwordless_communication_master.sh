#ssh-keygen
echo "65536" | sudo su - aldo -c "ssh-keygen -t rsa -f /home/aldo/.ssh/id_rsa -q -P "65536""

# REMOVE PASSWORD CHECK
for slave in slave1 slave2 slave3 slave4
    do
        echo "65536" | sudo su - aldo -c "ssh-keyscan $slave > .ssh/known_hosts"
        echo "65536" | sudo su - aldo -c "sshpass -p "65536" ssh-copy-id aldo@$slave"
    done

# REMOVE PASSWORD CHECK
echo "65536" | sudo su - aldo -c "eval `ssh-agent -s`"
echo "65536" | sudo su - aldo -c "sshpass -p "65536" ssh-add"
