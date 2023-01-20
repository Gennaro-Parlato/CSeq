void *__cs_safe_malloc(unsigned int __cs_size) {
	void *__cs_ptr = malloc(__cs_size);
	return __cs_ptr;
}

void __cs_init_scalar(void *__cs_var, unsigned int __cs_size) {
	if (__cs_size == sizeof(int))
		*(int *)__cs_var = __CSEQ_nondet_int();
	else {
		__cs_var = malloc(__cs_size);
	}
}

int __cs_exit(void *__cs_value_ptr, unsigned int __cs_thread_index) {
	return 0;
}

void __CSEQ_message(char *__cs_message) { ; }

int __cs_self(void) { return 1; }

void assume_abort_if_not(int cond) { __CPROVER_assume(cond); }
