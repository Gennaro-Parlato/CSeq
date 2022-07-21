"""
    General setting for CSeq
"""
# Log will be write by date in year/month directory
logpath = "logs"
reportpath = "reports"

# Relative path to dependencies, calling environment
relpath = {}
relpath["preprocessor"] = ""
relpath["translatorDistributed"] = "cseq-feeder-master-slave.py"
relpath["translator"] = "cseq-feeder.py"