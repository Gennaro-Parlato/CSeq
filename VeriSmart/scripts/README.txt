
CONFIGURE EACH EC2 MACHINE (BOTH MASTER AND SLAVES) WITH THIS USERDATA:
enable_ssm_on_instances_master_slaves.sh

MASTER:
initialize_libraries_master.sh
{CLONE VERISMART INSIDE MASTER}
initialize_verismart_master.sh

SLAVES:
automatic_configuration_slave.sh

MASTER:
enable_passwordless_communication_master.sh