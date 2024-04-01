#ifndef __prover
#define __prover

#include "linear_gkr/circuit_fast_track.h"
#include "linear_gkr/prime_field.h"
#include "linear_gkr/polynomial.h"
#include <cstring>
#include <utility>
#include <chrono>
#include <iostream>
#include<emp-tool/emp-tool.h> // for NetIO, etc
#include<emp-ot/emp-ot.h>   // for OTs

using namespace std;
class prover
{
public:
	enum class MPSPDZ_CMD {
		matmul,
		merge
	};
	//mpc
	int client;
	int clientSocket1,clientSocket2;
	int prover_id;
	int communication_total=0;

	//interact functions with MPSPDZ
	double* do_something();
	void change_dir(string dir);
	void feed_MPSPDZ_matmul_input(prime_field::field_element** A, prime_field::field_element** B);
	void feed_MPSPDZ_merge_input(prime_field::field_element* input,int size);

	prime_field::field_element* read_MPSPDZ_output(MPSPDZ_CMD cmd,int size);
	void write_MPSDPZ_input_1D(string MPSPDZ_dir, string MPSPDZ_input_dir, prime_field::field_element* input_vector, int size);

	void write_MPSDPZ_input_2D(string MPSPDZ_dir, string MPSPDZ_input_dir,prime_field::field_element** input_matrix);
	void run_MPSPDZ(string mpspdz_dir,string compile_cmd,string run_cmd);
	prime_field::field_element* multiply(int size,prime_field::field_element* op1,prime_field::field_element* op2);//dotprod
	
	prime_field::field_element* matmul(prime_field::field_element** A,prime_field::field_element** B);//dotprod
	void generate_MPSPDZ_cmd_and_run(MPSPDZ_CMD cmd_type,int merge_size);

	prime_field::field_element* merge_vector(prime_field::field_element* share,int n);
	prime_field::field_element merge(prime_field::field_element share);
	prime_field::field_element merge_setup();
	prime_field::field_element merge_WAN(prime_field::field_element share);
	// void send(prime_field::field_element share,string pipe_name);
	// prime_field::field_element recv(string pipe_name);

	prime_field::field_element* merge_vector_proof(prime_field::field_element* share,int n);
	prime_field::field_element merge_proof(prime_field::field_element share);
	prime_field::field_element* merge_proofs(prime_field::field_element* share, int n);

	//add matrix multiplication
	int matrix_size;int n;int m;int o;
	prime_field::field_element **A, **B;
	prime_field::field_element *result_flat;
	void get_matrices_convolution(prime_field::field_element** A_from_verifier,prime_field::field_element** B_from_verifier,int,int n_from_v, int m_from_v,int o_from_v);
	void get_matrices(prime_field::field_element** A_from_verifier,prime_field::field_element** B_from_verifier,int);
	std::pair<std::vector<std::vector<prime_field::field_element>>, std::vector<prime_field::field_element>> convolutionAsMatrixVector(const std::vector<std::vector<prime_field::field_element>>& input, 
	const std::vector<std::vector<prime_field::field_element>>& kernel, int inputHeight, int inputWidth, int kernelSize,int padding,int numInChannel);

	// prime_field::field_element merge(prime_field::field_element number,int prover_id);
	int bit_length_matrix;
	int total_uv_matrix;

	void init_array_matrix(int);
	void sumcheck_init_matrix(const prime_field::field_element*, const prime_field::field_element*, const prime_field::field_element*, const prime_field::field_element*);
	void sumcheck_phase1_init_matrix();//compute the matrix table
	quadratic_poly sumcheck_phase1_update_matrix(prime_field::field_element, int);

	const prime_field::field_element *g,*h,*one_minus_g,*one_minus_h;
	linear_poly *A_poly,*B_poly,*C_poly;
	prime_field::field_element** matrix_multiplication();

	double evaluation_time_matrix;
	double total_time_matrix;

//===================================================

	prime_field::field_element rand_ss;
	prime_field::field_element v_u, v_v;//secret shared
	int total_uv;
	layered_circuit C;
	prime_field::field_element* circuit_value[1000000];
	prime_field::field_element* circuit_value_shared[1000000];


	int sumcheck_layer_id, length_g, length_u, length_v;
	prime_field::field_element alpha, beta;
	const prime_field::field_element *r_0, *r_1;
	prime_field::field_element *one_minus_r_0, *one_minus_r_1;

	linear_poly *addV_array;//max number of gates
	linear_poly *V_mult_add;//max number of gates,secret shared
	prime_field::field_element *beta_u;
	prime_field::field_element *beta_g_r0_fhalf, *beta_g_r0_shalf, *beta_g_r1_fhalf, *beta_g_r1_shalf, *beta_u_fhalf, *beta_u_shalf;
	prime_field::field_element *beta_g_sum;
	linear_poly *add_mult_sum;//max number of gates, secret shared
	double total_time;
	void init_array(int);
	void get_circuit(const layered_circuit &from_verifier);
	prime_field::field_element* evaluate();
	void proof_init();
	void sumcheck_init(int layer_id, int bit_length_g, int bit_length_u, int bit_length_v, const prime_field::field_element &,
		const prime_field::field_element &, const prime_field::field_element*, const prime_field::field_element*, prime_field::field_element*, prime_field::field_element*);
	void sumcheck_phase1_init();
	void sumcheck_phase2_init(prime_field::field_element, const prime_field::field_element*, const prime_field::field_element*);
	
	quadratic_poly sumcheck_phase1_update(prime_field::field_element, int);
	quadratic_poly sumcheck_phase2_update(prime_field::field_element, int);
	prime_field::field_element V_res(const prime_field::field_element*, const prime_field::field_element*, const prime_field::field_element*, int, int);
	std::pair<prime_field::field_element, prime_field::field_element> sumcheck_finalize(prime_field::field_element);
	prime_field::field_element multiply(prime_field::field_element, prime_field::field_element, int);

	//check all communication
	void delete_self();
	prover()
	{
		memset(circuit_value, 0, sizeof circuit_value);
	}
	~prover();
};

#endif
