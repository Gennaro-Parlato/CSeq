# now aldo's account of master EC2 instance should share a folder which contains the verismart project
# through NFS-Server which allows master to export the directory of the project such that it can share verismart with all slaves
# slaves will mount that directory to exchange data and project changes
# so open the master terminal and execute
# log in again in aldo's account and clone the verismart project
# such that CSeq folder will be the shared folder among EC2 instances:

#git clone https://github.com/Gennaro-Parlato/CSeq.git
#su - aldo -c "unzip CSeq.zip"

sudo pip3 install -r /home/aldo/CSeq/VeriSmart/requirements.txt

# now go back to master terminal and run distributed version of verismart:
# create a nodes_list file where to store all the partecipants hostname which will partecipate in the execution:
#add the list of hostnames of each node with default number of slots and maximum number of slots:
echo "master slots=1" | sudo tee -a /home/aldo/CSeq/VeriSmart/nodes
echo "slave1 slots=1" | sudo tee -a /home/aldo/CSeq/VeriSmart/nodes
echo "slave2 slots=1" | sudo tee -a /home/aldo/CSeq/VeriSmart/nodes
echo "slave3 slots=1" | sudo tee -a /home/aldo/CSeq/VeriSmart/nodes
echo "slave4 slots=1" | sudo tee -a /home/aldo/CSeq/VeriSmart/nodes

#master declares that will share the project folder with slaves:
echo "/home/aldo/CSeq/VeriSmart *(rw,sync,no_root_squash,no_subtree_check)" | sudo tee -a /etc/exports

#export the project folder to all slaves
#run this command every time a change has been done:
sudo exportfs -a

#restart NFS-Server service:
sudo service nfs-kernel-server restart
