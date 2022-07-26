
echo "$1 $2" | sudo tee -a /etc/hosts
echo "$1 slots=$3" | sudo tee -a /home/aldo/CSeq-master/VeriSmart/nodes

echo "slave6 10.0.0.182" | sudo tee -a /etc/hosts
echo "slave6 slots=1" | sudo tee -a /home/aldo/CSeq-master/VeriSmart/nodes
sudo ssh-keyscan slave6 | sudo tee -a /home/aldo/.ssh/known_hosts
