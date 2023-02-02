all :
	clang -Wall -O3 test_ssh_bench_new_keys.c -o bench_new_keys
	clang -Wall -O3 test_ssh_bench_client_dh_init.c -o bench_client
	clang -Wall -O3 test_ssh_bench_server_dh_reply.c -o bench_server
	./bench_new_keys
	./bench_client
	./bench_server
	rm bench_new_keys
	rm bench_client
	rm bench_server
