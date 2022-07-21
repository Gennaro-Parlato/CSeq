
CONFIGURE EACH EC2 MACHINE (BOTH MASTER AND SLAVES) WITH THIS USERDATA:
sudo snap install amazon-ssm-agent --classic
sudo systemctl start amazon-ssm-agent
sudo systemctl enable amazon-ssm-agent

MASTER:
initialize_libraries.sh
initialize_verismart_master.sh

SLAVES:
automatic_configuration_slave.sh

MASTER:
enable_passwordless_communication_master.sh