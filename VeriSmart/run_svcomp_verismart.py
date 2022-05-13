import argparse

# ---------------- Configs ----------------------------------------------------
import re
import subprocess
from time import time

pthread = {
    'relative_path': 'pthread',
    'files': ['bigshot_p.c', 'bigshot_s.c', 'bigshot_s2.c', 'fib_bench-1.c', 'fib_bench-2.c', 'fib_bench_longer-1.c',
              'fib_bench_longer-2.c', 'fib_bench_longest-1.c', 'fib_bench_longest-2.c', 'indexer.c', 'lazy01.c',
              'queue.c', 'queue_longer.c', 'queue_longest.c', 'queue_ok.c', 'queue_ok_longer.c', 'queue_ok_longest.c',
              'reorder_2.c', 'reorder_5.c', 'sigma.c', 'singleton.c', 'singleton_with-uninit-problems.c', 'stack-1.c',
              'stack-2.c', 'stack_longer-1.c', 'stack_longer-2.c', 'stack_longest-1.c', 'stack_longest-2.c',
              'stateful01-1.c', 'stateful01-2.c', 'sync01.c', 'triangular-1.c', 'triangular-2.c',
              'triangular-longer-1.c', 'triangular-longer-2.c', 'triangular-longest-1.c', 'triangular-longest-2.c',
              'twostage_3.c']
}

pthread_atomic = {
    'relative_path': 'pthread-atomic',
    'files': ['dekker.c', 'gcd-2.c', 'lamport.c', 'peterson.c', 'qrcu-1.c', 'qrcu-2.c', 'read_write_lock-1.c',
              'read_write_lock-2.c', 'scull.c', 'szymanski.c', 'time_var_mutex.c']
}

pthread_ext = {
    'relative_path': 'pthread-ext',
    'files':
        ['01_inc.c', '02_inc_cas.c', '03_incdec.c', '04_incdec_cas.c', '05_tas.c', '06_ticket.c', '07_rand.c',
         '08_rand_cas.c', '09_fmaxsym.c', '10_fmaxsym_cas.c', '11_fmaxsymopt.c', '12_fmaxsymopt_cas.c', '13_unverif.c',
         '14_spin2003.c', '15_dekker.c', '16_peterson.c', '17_szymanski.c', '18_read_write_lock.c',
         '19_time_var_mutex.c', '20_lamport.c', '23_lu-fig2.fixed.c', '25_stack.c', '25_stack_longer-1.c',
         '25_stack_longer-2.c', '25_stack_longest-1.c', '25_stack_longest-2.c', '26_stack_cas.c',
         '26_stack_cas_longer-1.c', '26_stack_cas_longer-2.c', '26_stack_cas_longest-1.c', '26_stack_cas_longest-2.c',
         '27_Boop_simple_vf.c', '28_buggy_simple_loop1_vf.c', '29_conditionals_vs.c', '30_Function_Pointer3_vs.c',
         '31_simple_loop5_vs.c', '32_pthread5_vs.c', '33_double_lock_p1_vs.c', '34_double_lock_p2_vs.c',
         '35_double_lock_p3_vs.c', '36_stack_cas_p0_vs_concur.c', '37_stack_lock_p0_vs_concur.c',
         '38_rand_cas_vs_concur.c', '39_rand_lock_p0_vs.c', '40_barrier_vf.c', '41_FreeBSD_abd_kbd_sliced.c',
         '42_FreeBSD_rdma_addr_sliced.c', '43_NetBSD_sysmon_power_sliced.c', '44_Solaris_space_map_sliced.c',
         '45_monabsex1_vs.c', '46_monabsex2_vs.c', '47_ticket_lock_hc_backoff_vs.c',
         '48_ticket_lock_low_contention_vs.c']
}

pthread_wmm = {
    'relative_path': 'pthread-wmm',
    'files':
        [
            'mix000_power.oepc.c', 'mix000_power.opt.c', 'mix000_pso.oepc.c', 'mix000_pso.opt.c', 'mix000_rmo.oepc.c',
            'mix000_rmo.opt.c', 'mix000_tso.oepc.c', 'mix000_tso.opt.c', 'mix001_power.oepc.c', 'mix001_power.opt.c',
            'mix001_pso.oepc.c', 'mix001_pso.opt.c', 'mix001_rmo.oepc.c', 'mix001_rmo.opt.c', 'mix001_tso.oepc.c',
            'mix001_tso.opt.c', 'mix002_power.oepc.c', 'mix002_power.opt.c', 'mix002_pso.oepc.c', 'mix002_pso.opt.c',
            'mix002_rmo.oepc.c', 'mix002_rmo.opt.c', 'mix002_tso.oepc.c', 'mix002_tso.opt.c', 'mix003_power.oepc.c',
            'mix003_power.opt.c', 'mix003_pso.oepc.c', 'mix003_pso.opt.c', 'mix003_rmo.oepc.c', 'mix003_rmo.opt.0.1.c',
            'mix003_rmo.opt.0.c', 'mix003_rmo.opt.c', 'mix003_tso.oepc.c', 'mix003_tso.opt.c', 'mix004_power.oepc.c',
            'mix004_power.opt.c', 'mix004_pso.oepc.c', 'mix004_pso.opt.c', 'mix004_rmo.oepc.c', 'mix004_rmo.opt.c',
            'mix004_tso.oepc.c', 'mix004_tso.opt.c', 'mix005_power.oepc.c', 'mix005_power.opt.c', 'mix005_pso.oepc.c',
            'mix005_pso.opt.c', 'mix005_rmo.oepc.c', 'mix005_rmo.opt.c', 'mix005_tso.oepc.c', 'mix005_tso.opt.c',
            'mix006_power.oepc.c', 'mix006_power.opt.c', 'mix006_pso.oepc.c', 'mix006_pso.opt.c', 'mix006_rmo.oepc.c',
            'mix006_rmo.opt.c', 'mix006_tso.oepc.c', 'mix006_tso.opt.c', 'mix007_power.oepc.c', 'mix007_power.opt.c',
            'mix007_pso.oepc.c', 'mix007_pso.opt.c', 'mix007_rmo.oepc.c', 'mix007_rmo.opt.c', 'mix007_tso.oepc.c',
            'mix007_tso.opt.c', 'mix008_power.oepc.c', 'mix008_power.opt.c', 'mix008_pso.oepc.c', 'mix008_pso.opt.c',
            'mix008_rmo.oepc.c', 'mix008_rmo.opt.c', 'mix008_tso.oepc.c', 'mix008_tso.opt.c', 'mix009_power.oepc.c',
            'mix009_power.opt.c', 'mix009_pso.oepc.c', 'mix009_pso.opt.c', 'mix009_rmo.oepc.c', 'mix009_rmo.opt.c',
            'mix009_tso.oepc.c', 'mix009_tso.opt.c', 'mix010_power.oepc.c', 'mix010_power.opt.c', 'mix010_pso.oepc.c',
            'mix010_pso.opt.c', 'mix010_rmo.oepc.c', 'mix010_rmo.opt.c', 'mix010_tso.oepc.c', 'mix010_tso.opt.c',
            'mix011_power.oepc.c', 'mix011_power.opt.c', 'mix011_pso.oepc.c', 'mix011_pso.opt.c', 'mix011_rmo.oepc.c',
            'mix011_rmo.opt.c', 'mix011_tso.oepc.c', 'mix011_tso.opt.c', 'mix012_power.oepc.c', 'mix012_power.opt.c',
            'mix012_pso.oepc.c', 'mix012_pso.opt.c', 'mix012_rmo.oepc.c', 'mix012_rmo.opt.c', 'mix012_tso.oepc.c',
            'mix012_tso.opt.c', 'mix013_power.oepc.c', 'mix013_power.opt.c', 'mix013_pso.oepc.c', 'mix013_pso.opt.c',
            'mix013_rmo.oepc.c', 'mix013_rmo.opt.c', 'mix013_tso.oepc.c', 'mix013_tso.opt.c', 'mix014_power.oepc.c',
            'mix014_power.opt.c', 'mix014_pso.oepc.c', 'mix014_pso.opt.c', 'mix014_rmo.oepc.c', 'mix014_rmo.opt.c',
            'mix014_tso.oepc.c', 'mix014_tso.opt.c', 'mix015_power.oepc.c', 'mix015_power.opt.c', 'mix015_pso.oepc.c',
            'mix015_pso.opt.c', 'mix015_rmo.oepc.c', 'mix015_rmo.opt.c', 'mix015_tso.oepc.c', 'mix015_tso.opt.c',
            'mix016_power.oepc.c', 'mix016_power.opt.c', 'mix016_pso.oepc.c', 'mix016_pso.opt.c', 'mix016_rmo.oepc.c',
            'mix016_rmo.opt.c', 'mix016_tso.oepc.c', 'mix016_tso.opt.c', 'mix017_power.oepc.c', 'mix017_power.opt.c',
            'mix017_pso.oepc.c', 'mix017_pso.opt.c', 'mix017_rmo.oepc.c', 'mix017_rmo.opt.c', 'mix017_tso.oepc.c',
            'mix017_tso.opt.c', 'mix018_power.oepc.c', 'mix018_power.opt.c', 'mix018_pso.oepc.c', 'mix018_pso.opt.c',
            'mix018_rmo.oepc.c', 'mix018_rmo.opt.c', 'mix018_tso.oepc.c', 'mix018_tso.opt.c', 'mix019_power.oepc.c',
            'mix019_power.opt.c', 'mix019_pso.oepc.c', 'mix019_pso.opt.c', 'mix019_rmo.oepc.c', 'mix019_rmo.opt.c',
            'mix019_tso.oepc.c', 'mix019_tso.opt.c', 'mix020_power.oepc.c', 'mix020_power.opt.c', 'mix020_pso.oepc.c',
            'mix020_pso.opt.c', 'mix020_rmo.oepc.c', 'mix020_rmo.opt.c', 'mix020_tso.oepc.c', 'mix020_tso.opt.c',
            'mix021_power.oepc.c', 'mix021_power.opt.c', 'mix021_pso.oepc.c', 'mix021_pso.opt.c', 'mix021_rmo.oepc.c',
            'mix021_rmo.opt.c', 'mix021_tso.oepc.c', 'mix021_tso.opt.c', 'mix022_power.oepc.c', 'mix022_power.opt.c',
            'mix022_pso.oepc.c', 'mix022_pso.opt.c', 'mix022_rmo.oepc.c', 'mix022_rmo.opt.c', 'mix022_tso.oepc.c',
            'mix022_tso.opt.c', 'mix023_power.oepc.c', 'mix023_power.opt.c', 'mix023_pso.oepc.c', 'mix023_pso.opt.c',
            'mix023_rmo.oepc.c', 'mix023_rmo.opt.c', 'mix023_tso.oepc.c', 'mix023_tso.opt.c', 'mix024_power.oepc.c',
            'mix024_power.opt.c', 'mix024_pso.oepc.c', 'mix024_pso.opt.c', 'mix024_rmo.oepc.c', 'mix024_rmo.opt.c',
            'mix024_tso.oepc.c', 'mix024_tso.opt.c', 'mix025_power.oepc.c', 'mix025_power.opt.c', 'mix025_pso.oepc.c',
            'mix025_pso.opt.c', 'mix025_rmo.oepc.c', 'mix025_rmo.opt.c', 'mix025_tso.oepc.c', 'mix025_tso.opt.c',
            'mix026_power.oepc.c', 'mix026_power.opt.c', 'mix026_pso.oepc.c', 'mix026_pso.opt.c', 'mix026_rmo.oepc.c',
            'mix026_rmo.opt.c', 'mix026_tso.oepc.c', 'mix026_tso.opt.c', 'mix027_power.oepc.c', 'mix027_power.opt.c',
            'mix027_pso.oepc.c', 'mix027_pso.opt.c', 'mix027_rmo.oepc.c', 'mix027_rmo.opt.c', 'mix027_tso.oepc.c',
            'mix027_tso.opt.c', 'mix028_power.oepc.c', 'mix028_power.opt.c', 'mix028_pso.oepc.c', 'mix028_pso.opt.c',
            'mix028_rmo.oepc.c', 'mix028_rmo.opt.c', 'mix028_tso.oepc.c', 'mix028_tso.opt.c', 'mix029_power.oepc.c',
            'mix029_power.opt.c', 'mix029_pso.oepc.c', 'mix029_pso.opt.c', 'mix029_rmo.oepc.c', 'mix029_rmo.opt.c',
            'mix029_tso.oepc.c', 'mix029_tso.opt.c', 'mix030_power.oepc.c', 'mix030_power.opt.c', 'mix030_pso.oepc.c',
            'mix030_pso.opt.c', 'mix030_rmo.oepc.c', 'mix030_rmo.opt.c', 'mix030_tso.oepc.c', 'mix030_tso.opt.c',
            'mix031_power.oepc.c', 'mix031_power.opt.c', 'mix031_pso.oepc.c', 'mix031_pso.opt.c', 'mix031_rmo.oepc.c',
            'mix031_rmo.opt.c', 'mix031_tso.oepc.c', 'mix031_tso.opt.c', 'mix032_power.oepc.c', 'mix032_power.opt.c',
            'mix032_pso.oepc.c', 'mix032_pso.opt.c', 'mix032_rmo.oepc.c', 'mix032_rmo.opt.c', 'mix032_tso.oepc.c',
            'mix032_tso.opt.c', 'mix033_power.oepc.c', 'mix033_power.opt.c', 'mix033_pso.oepc.c', 'mix033_pso.opt.c',
            'mix033_rmo.oepc.c', 'mix033_rmo.opt.c', 'mix033_tso.oepc.c', 'mix033_tso.opt.c', 'mix034_power.oepc.c',
            'mix034_power.opt.c', 'mix034_pso.oepc.c', 'mix034_pso.opt.c', 'mix034_rmo.oepc.c', 'mix034_rmo.opt.c',
            'mix034_tso.oepc.c', 'mix034_tso.opt.c', 'mix035_power.oepc.c', 'mix035_power.opt.c', 'mix035_pso.oepc.c',
            'mix035_pso.opt.c', 'mix035_rmo.oepc.c', 'mix035_rmo.opt.c', 'mix035_tso.oepc.c', 'mix035_tso.opt.c',
            'mix036_power.oepc.c', 'mix036_power.opt.c', 'mix036_pso.oepc.c', 'mix036_pso.opt.c', 'mix036_rmo.oepc.c',
            'mix036_rmo.opt.c', 'mix036_tso.oepc.c', 'mix036_tso.opt.c', 'mix037_power.oepc.c', 'mix037_power.opt.c',
            'mix037_pso.oepc.c', 'mix037_pso.opt.c', 'mix037_rmo.oepc.c', 'mix037_rmo.opt.c', 'mix037_tso.oepc.c',
            'mix037_tso.opt.c', 'mix038_power.oepc.c', 'mix038_power.opt.c', 'mix038_pso.oepc.c', 'mix038_pso.opt.c',
            'mix038_rmo.oepc.c', 'mix038_rmo.opt.c', 'mix038_tso.oepc.c', 'mix038_tso.opt.c', 'mix039_power.oepc.c',
            'mix039_power.opt.c', 'mix039_pso.oepc.c', 'mix039_pso.opt.c', 'mix039_rmo.oepc.c', 'mix039_rmo.opt.c',
            'mix039_tso.oepc.c', 'mix039_tso.opt.c', 'mix040_power.oepc.c', 'mix040_power.opt.c', 'mix040_pso.oepc.c',
            'mix040_pso.opt.c', 'mix040_rmo.oepc.c', 'mix040_rmo.opt.c', 'mix040_tso.oepc.c', 'mix040_tso.opt.c',
            'mix041_power.oepc.c', 'mix041_power.opt.c', 'mix041_pso.oepc.c']
}
pthread_lit = {
    'relative_path': 'pthread-lit',
    'files':
        ['fk2012.c', 'fkp2013-1.c', 'fkp2013-2.c', 'fkp2013_variant-1.c', 'fkp2013_variant-2.c', 'fkp2014.c',
         'qw2004-1.c', 'qw2004-2.c', 'qw2004_variant.c', 'sssc12.c', 'sssc12_variant.c']
}

ldv_races = {
    'relative_path': 'ldv-races',
    'files': [
        'race-1_1-join.c', 'race-1_2-join.c', 'race-1_3-join.c', 'race-2_1-container_of.c', 'race-2_2-container_of.c',
        'race-2_3-container_of.c', 'race-2_4-container_of.c', 'race-2_5-container_of.c',
        'race-3_1-container_of-global.c', 'race-3_2-container_of-global.c', 'race-4_1-thread_local_vars.c',
        'race-4_2-thread_local_vars.c'
    ]
}

pthread_complex = {
    'relative_path': 'pthread-complex',
    'files': ['bounded_buffer.c	', 'elimination_backoff_stack.c	', 'safestack_relacy.c',
              'workstealqueue_mutex-1.c', 'workstealqueue_mutex-2.c	']
}

pthread_driver_races = {
    'relative_path': 'pthread-driver-races',
    'files': [
        'char_generic_nvram_nvram_llseek_nvram_unlocked_ioctl.c', 'char_generic_nvram_nvram_llseek_read_nvram.c',
        'char_generic_nvram_nvram_llseek_write_nvram.c', 'char_generic_nvram_nvram_unlocked_ioctl_write_nvram.c',
        'char_generic_nvram_read_nvram_nvram_unlocked_ioctl.c', 'char_generic_nvram_read_nvram_write_nvram.c',
        'char_pc8736x_gpio_pc8736x_gpio_change_pc8736x_gpio_configure.c',
        'char_pc8736x_gpio_pc8736x_gpio_change_pc8736x_gpio_current.c',
        'char_pc8736x_gpio_pc8736x_gpio_change_pc8736x_gpio_get.c',
        'char_pc8736x_gpio_pc8736x_gpio_change_pc8736x_gpio_set.c',
        'char_pc8736x_gpio_pc8736x_gpio_configure_pc8736x_gpio_current.c',
        'char_pc8736x_gpio_pc8736x_gpio_configure_pc8736x_gpio_get.c',
        'char_pc8736x_gpio_pc8736x_gpio_configure_pc8736x_gpio_set.c',
        'char_pc8736x_gpio_pc8736x_gpio_current_pc8736x_gpio_get.c',
        'char_pc8736x_gpio_pc8736x_gpio_current_pc8736x_gpio_set.c',
        'char_pc8736x_gpio_pc8736x_gpio_get_pc8736x_gpio_set.c',
        'char_pc8736x_gpio_pc8736x_gpio_open_pc8736x_gpio_change.c',
        'char_pc8736x_gpio_pc8736x_gpio_open_pc8736x_gpio_configure.c',
        'char_pc8736x_gpio_pc8736x_gpio_open_pc8736x_gpio_current.c',
        'char_pc8736x_gpio_pc8736x_gpio_open_pc8736x_gpio_get.c',
        'char_pc8736x_gpio_pc8736x_gpio_open_pc8736x_gpio_set.c'
    ]
}

pthread_c_dac = {
    'relative_path': 'pthread-C-DAC',
    'files': ['pthread-demo-datarace-1.c', 'pthread-demo-datarace-2.c', 'pthread-finding-k-matches.c',
              'pthread-numerical-integration.c']
}

pthread_divine = {
    'relative_path': 'pthread-divine',
    'files': ['barrier_2t.c', 'barrier_3t.c', 'condvar.c', 'condvar_spurious_wakeup.c', 'divinefifo-bug_1w1r.c',
              'divinefifo_1w1r.c', 'one_time_barrier_2t.c', 'one_time_barrier_3t.c', 'one_time_barrier_twice_2t.c',
              'one_time_barrier_twice_3t.c', 'ring_1w1r-1.c', 'ring_1w1r-2.c', 'ring_2w1r-1.c', 'ring_2w1r-2.c',
              'tls_basic.c', 'tls_destructor_worker.c']
}

pthread_nondet = {
    'relative_path': 'pthread-nondet',
    'files': ['nondet-array-1.c', 'nondet-array-2.c', 'nondet-loop-bound-1.c', 'nondet-loop-bound-2.c',
              'nondet-loop-bound-variant-1.c', 'nondet-loop-bound-variant-2.c']
}
categories = [
   pthread, pthread_atomic, pthread_ext, pthread_wmm, pthread_lit, ldv_races, pthread_complex, pthread_driver_races,
   pthread_c_dac, pthread_divine, pthread_nondet
]

#categories = [
#    pthread_complex
#]
# -----------------------------------------------------------------------------
# ------------------------------Command line params setup----------------------

parser = argparse.ArgumentParser(description='Run svcomp suite using lazyseq and cbmc')
parser.add_argument('base_path', type=str, help='Path to base folder containing svcomp files')
parser.add_argument('--unwind', default=3, type=int,
                    help='How many iterations loops should be unwound for')
parser.add_argument('--rounds', default=3, type=int,
                    help='Rounds for round-robin')
parser.add_argument('--timeout', default=3600, type=int, help='Timeout for cbmc in seconds')
parser.add_argument('--dr', action='store_true', default=False,
                    help='Run with data race detection, defaults to false')

args = parser.parse_args()

base_file_path = args.base_path
unwind_bound = args.unwind
rounds_bound = args.rounds
timeout = args.timeout
is_data_race_mode = args.dr
dr_str = ''
if is_data_race_mode:
    dr_str = '--dr'
# -----------------------------------------------------------------------------

if __name__ == '__main__':
    results = dict()
    for category in categories:
        for f in category['files']:
            filepath = base_file_path + '/' + category['relative_path'] + '/' + f
            print('./verismart.py -i %s --unwind %d --rounds %d --seq --debug' % (
                filepath, unwind_bound, rounds_bound) + dr_str)
            start_time = time()
            p = subprocess.Popen(
                ['./verismart.py -i %s --unwind %d --rounds %d --seq --debug ' % (
                    filepath, unwind_bound, rounds_bound) + dr_str],
                stdout=subprocess.PIPE, shell=True)
            output = p.stdout.read()
            end_time = time()
            if category['relative_path'] not in results:
                results[category['relative_path']] = dict()
            if f not in results[category['relative_path']]:
                results[category['relative_path']][f] = dict()
            if 'Sequentialization successfully completed' in output.decode():
                results[category['relative_path']][f]['seq_result'] = 'SUCCESS'
                prefix = '_cs'
                if is_data_race_mode:
                    prefix += 'dr'
                prefix += '_'
                seq_filepath = base_file_path + '/' + category['relative_path'] + '/' + prefix + f
                p = subprocess.Popen(
                    ['wc -l %s' % (seq_filepath)],
                    stdout=subprocess.PIPE, shell=True)
                output = p.stdout.read()
                length = re.findall('(.*) .*', output.decode())[0]
                results[category['relative_path']][f]['seq_length'] = length
            else:
                results[category['relative_path']][f]['seq_result'] = 'SEQ ERROR'
            results[category['relative_path']][f]['seq_time'] = end_time - start_time

    for category in categories:
        for f in category['files']:
            prefix = '_cs'
            if is_data_race_mode:
                prefix += 'dr'
            prefix += '_'
            filepath = base_file_path + '/' + category['relative_path'] + '/' + prefix + f

            print('timeout 10 -k %d ./cbmc %s --unwind %d --no-unwinding-assertions --stop-on-fail' % (
                timeout, filepath, unwind_bound))
            start_time = time()
            p = subprocess.Popen(
                ['timeout -k 10 %d ./cbmc %s --unwind %d --no-unwinding-assertions --stop-on-fail' % (
                    timeout, filepath, unwind_bound)],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
            output = p.stdout.read()
            end_time = time()
            time_taken = end_time - start_time
            if 'VERIFICATION FAILED' in output.decode():
                results[category['relative_path']][f]['cbmc_result'] = 'P'
            elif 'VERIFICATION SUCCESSFUL' in output.decode():
                results[category['relative_path']][f]['cbmc_result'] = 'N'
            elif 'core dumped' in output.decode():
                results[category['relative_path']][f]['cbmc_result'] = 'CBMC ERROR'
            else:
                results[category['relative_path']][f]['cbmc_result'] = 'TIMEOUT'

            if results[category['relative_path']][f]['cbmc_result'] in ('P', 'N'):
                try:
                    vars_amount = re.findall('(.+) variables,', output.decode())[0]
                    clauses_amount = re.findall('variables, (.+) clauses\n', output.decode())[0]
                    solver_time = re.findall('Runtime Solver: (.+)s\n', output.decode())[0]
                    results[category['relative_path']][f]['variables'] = vars_amount
                    results[category['relative_path']][f]['clauses'] = clauses_amount
                    results[category['relative_path']][f]['solver_time'] = solver_time
                except:
                    pass
            results[category['relative_path']][f]['total_time'] = time_taken + results[category['relative_path']][f][
                'seq_time']

    output = ["file,result,seq-length,Total Time, variables, clauses, SAT-solver time "]
    for category in categories:
        for f in category['files']:
            try:
                line = category['relative_path'] + '/' + f + ','
                if results[category['relative_path']][f]['seq_result'] == 'SEQ ERROR':
                    line += 'SEQ ERROR'
                else:
                    line += results[category['relative_path']][f]['cbmc_result']
                line += ','
                if 'seq_length' in results[category['relative_path']][f]:
                    line += results[category['relative_path']][f]['seq_length']
                line += ','
                line += str(results[category['relative_path']][f]['total_time']) + ','
                if 'variables' in results[category['relative_path']][f]:
                    line += results[category['relative_path']][f]['variables']
                line += ','
                if 'clauses' in results[category['relative_path']][f]:
                    line += results[category['relative_path']][f]['clauses']
                line += ','
                if 'solver_time' in results[category['relative_path']][f]:
                    line += results[category['relative_path']][f]['solver_time']
                output.append(line)
            except Exception as e:
                print(e)
                print(results[category['relative_path']][f])
    output_str = '\n'.join(output)
    f = open('results.csv', 'w')
    f.write(output_str)
    f.close()
