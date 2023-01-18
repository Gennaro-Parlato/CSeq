void *__cs_safe_malloc(unsigned int __cs_size) {
	void *__cs_ptr = malloc(__cs_size);
	return __cs_ptr;
}

int __cs_exit(void *__cs_value_ptr, unsigned int __cs_thread_index) {
	return 0;
}

void __CSEQ_message(char *__cs_message) { ; }

int __cs_self(void) { return 1; }

void assume_abort_if_not(int cond) { __CPROVER_assume(cond); }
