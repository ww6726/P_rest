#include "linear_gkr/verifier_fast_track.h"
#include <string>
#include <utility>
#include <iostream>
#include "linear_gkr/random_generator.h"
#include <bitset>
#include <cmath>
#include <iostream>
#include <filesystem>
#define ALICE 0
#define BOB 1
#define CAT 2
// #include <emp-sh2pc/emp-sh2pc.h>

using namespace std;
int compute_bit_length(int size)
{
	int n = size;
	int cnt = 0;
	//2 while loop to find the next power of 2
	while(n)
	{
		cnt++;
		n >>= 1;

	}
	n = 1;
	while(cnt)
	{
		n <<= 1;
		cnt--;
		
	}
	int mx = n;
	while(mx)
	{
		cnt++;
		mx >>= 1;
	}
	return cnt-1;

}
unsigned int nextPowerOf2(unsigned int n) {
    if (n == 0) {
        return 1;  // The next power of 2 after 0 is 2^0 = 1
    }

    // Find the position of the most significant bit (1) in n
    unsigned int bitPos = 0;
    n--;

    while (n > 0) {
        n >>= 1;
        bitPos++;
    }

    // Calculate and return the next power of 2
    return 1 << bitPos;
}

void verifier::create_maxpool_circuit(prime_field::field_element *inputs, int n)
{
	int d = 4;
	C.circuit = new layer[d];
	C.circuit[0].gates = new gate[2*n*Q];
	C.circuit[1].gates = new gate[n*Q];
	C.circuit[2].gates = new gate[n];
	C.circuit[3].gates = new gate[n];
	C.total_depth = d;
	int bq = 1;
	int g,ty;
	long long u, v;
	u = 0;
	long long *two_mul = new long long[Q];
	int idx = Q-1;

	for (int i = 0; i < Q; ++i)
	{
		two_mul[i] = pow(2,idx--);
		two_mul[i] = 0;

	}
	for(int k = 0; k < d; ++k)
	{
		if(k==0){//input layer
			for (int i = 0; i < n; ++i)
			{
				int index = 0;
				for (int j = 0; j < 2*Q; ++j)
				{
					if(j%2==0){
						C.circuit[0].gates[i*2*Q+j] = gate(3,u, 0);
					}else{
						C.circuit[0].gates[i*2*Q+j] = gate(3,two_mul[index++], 0);
					}
				}
			}
			C.circuit[0].bit_length = compute_bit_length(2*Q*n-1);		
		}
		else if(k==1){//multiplication layer
			int idx = 0;
			for (int i = 0; i < n; ++i)
			{
				for (int j = 0; j < Q; ++j)
				{
					ty = 1;//mul
					g = i*Q+j;
					u = idx;
					v = u+1;
					C.circuit[1].gates[g] = gate(1,u,v);
					idx+=2;
				}
			}

			C.circuit[1].bit_length = compute_bit_length(Q*n-1);
		}
		else if(k==2){//summation layer
			for (int i = 0; i < n; ++i)
			{
				ty = 5;//sum gate
				g = i;
				u = i*Q;
				v = i*Q+Q-1;
				C.circuit[2].gates[g] = gate(5,u,v);
			}
			C.circuit[2].bit_length = compute_bit_length(n-1);
		}
		else if(k==3){//sign-bit multiplication
			for (int i = 0; i < n; ++i)
			{
				ty = 1;//mul gate
				g = i;
				u = i;
				v = i;
				C.circuit[3].gates[g] = gate(1,u,v);
			}
			C.circuit[3].bit_length = compute_bit_length(n-1);
		}
	}
	int max_bit_length = C.circuit[0].bit_length;

	p -> init_array(max_bit_length);

	beta_g_r0 = new prime_field::field_element[(1 << max_bit_length)];
	beta_g_r1 = new prime_field::field_element[(1 << max_bit_length)];
	beta_v = new prime_field::field_element[(1 << max_bit_length)];
	beta_u = new prime_field::field_element[(1 << max_bit_length)];

}
void verifier::get_prover(prover *pp)
{
	p = pp;
}
void verifier::read_input_and_kernel(int conv_size, int kernel_size,int padding, int numInChannel)
{
    
	int inputSize = conv_size*conv_size;
    std::vector<prime_field::field_element> input(inputSize);
	std::vector<std::vector<prime_field::field_element>> input3D(inputSize, std::vector<prime_field::field_element>(numInChannel));

	for (int i = 0; i < inputSize; i++)
	{
		input[i] = i;
		for(int j = 0;j<numInChannel;j++){
			input3D[i][j] = 1;
		}
	}

	int kernelSize = kernel_size*kernel_size;

    std::vector<prime_field::field_element> kernel(kernelSize);
	std::vector<std::vector<prime_field::field_element>> kernel3D(kernelSize, std::vector<prime_field::field_element>(numInChannel));
	for (int i = 0; i < kernelSize; i++)
	{
		kernel[i] = i;
		for(int j = 0;j<numInChannel;j++){
			kernel3D[i][j] = 1;
		}
	}
    std::pair<std::vector<std::vector<prime_field::field_element>>, std::vector<prime_field::field_element>> converted_data = p->convolutionAsMatrixVector(input3D, kernel3D, conv_size, conv_size, kernel_size,padding,numInChannel);

	int rows = converted_data.first.size();
	int cols = converted_data.first[0].size();
	int kernel_len = converted_data.second.size();
	matrix_size = rows > cols ? rows : cols;
	matrix_size = nextPowerOf2(matrix_size);
	cout<<"matrix size: "<<matrix_size<<endl;
	cout<<rows<<" "<<cols<<" "<<kernel_len<<endl;
	n = rows;
	m = cols;
	o = 1;
	//initialize matrices
	A = new prime_field::field_element*[matrix_size];
	B = new prime_field::field_element*[matrix_size];
	for (int i = 0; i < matrix_size; ++i)
	{
		A[i] = new prime_field::field_element[matrix_size];
		B[i] = new prime_field::field_element[matrix_size];
		for (int j = 0; j < matrix_size; ++j)
		{
			A[i][j] = 1;
			B[i][j] = 1;
		}
	}
	//fill in matrices
	for(int i = 0; i < rows; ++i){
		for(int j = 0; j < cols; ++j){
			A[i][j] = converted_data.first[i][j];
		}
	}
	for(int i = 0; i < kernel_len; ++i){
		B[i][0] = converted_data.second[i];
	}





	int cnt = 0;
	int num_entries = matrix_size*matrix_size;
	while(num_entries)
	{
		cnt++;
		num_entries >>= 1;
	}
	cnt--;
	bit_length = cnt;
	p -> init_array_matrix(bit_length);

}
void verifier::read_input_matrices(int size)
{	
	matrix_size = size;
	A = new prime_field::field_element*[matrix_size];
	B = new prime_field::field_element*[matrix_size];

	for (int i = 0; i < matrix_size; ++i)
	{
		A[i] = new prime_field::field_element[matrix_size];
		B[i] = new prime_field::field_element[matrix_size];

		for (int j = 0; j < matrix_size; ++j)
		{
			A[i][j] = 231;
			B[i][j] = 1;

		}
	}
	int cnt = 0;
	int num_entries = matrix_size*matrix_size;
	while(num_entries)
	{
		cnt++;
		num_entries >>= 1;
	}
	cnt--;
	bit_length = cnt;
	p -> init_array_matrix(bit_length);
}

int* verifier::bitDecompose(prime_field::field_element number,int numBits)
{
	uint64 number_I = (uint64)(number.value.value_64%prime_field::mod);

	std::string binaryString;
    // Bit-decompose the number into a 12-bit binary string
    for (int i = numBits-1; i >= 0; i--) {
        int bit = (number_I >> i ) & 1;
        binaryString += std::to_string(bit);
    }
	int* bits = new int[numBits];
	for(int i=0;i<numBits;i++){
		bits[0] = static_cast<int>(binaryString[i]);
	}	
	return bits;
 
}
prime_field::field_element verifier::findMax(prime_field::field_element* inputs,int size){
	prime_field::field_element a = 4;

    prime_field::field_element max = inputs[0]; // Initialize max with the first element

    for (int i = 1; i < size; i++) {
        if (inputs[i] > max) {
            max = inputs[i];
        }
    }

    return max;
}
void verifier::create_accumulate_circuit(int* bits,int n)
{
	

}
void verifier::create_maxPool_circuit(prime_field::field_element* x, int n)
{	
	//these are provers' work, we put them here for testing
	prime_field::field_element max = findMax(x,n);
	prime_field::field_element* x_bar = new prime_field::field_element[n];//holds all the difference between max and x_i
	int** x_bits = new int*[n];
	int d = log2(n);
	C.circuit = new layer[d];
	C.circuit[0].gates = new gate[n*numBits];
	cout<<C.circuit[0].gate_idx<<endl;
	for(int i=0;i<n;i++){

		x_bar[i] = max - x[i];
		x_bits[i] = bitDecompose(x_bar[i],numBits);
		
		create_accumulate_circuit(x_bits[i],numBits);	
	}

	cout<<"i am here"<<endl;
	exit(1);
}
void verifier::compare_circuit(prime_field::field_element a, prime_field::field_element b)
{
	//prover needs to provide bits. 

}
void verifier::read_circuit(const char *path)
{

	int d;
	FILE *circuit_in;
	circuit_in = fopen(path, "r");

	fscanf(circuit_in, "%d", &d);

	int n;
	C.circuit = new layer[d + 1];
	C.total_depth = d + 1;
	int max_bit_length = -1;
	
	for(int i = 1; i <= d; ++i)
	{
		fscanf(circuit_in, "%d", &n);
		
		if(i != 1)
		{
			if(n == 1)
				C.circuit[i].gates = new gate[2];
			else
				C.circuit[i].gates = new gate[n];
		}
		else
		{
			if(n == 1)
			{
				C.circuit[0].gates = new gate[2];
				C.circuit[1].gates = new gate[2];
			}
			else
			{
				C.circuit[0].gates = new gate[n];
				C.circuit[1].gates = new gate[n];
			}
		}
		
		int max_gate = -1;
		int previous_g = -1;
		for(int j = 0; j < n; ++j)
		{
			int ty, g;
			long long u, v;
			fscanf(circuit_in, "%d%d%lld%lld", &ty, &g, &u, &v);
	
			if(ty == 6)
			{
				if(v != 0)
					fprintf(stderr, "WARNING, v!=0 for NOT gate.\n");
				v = 0;
			}
			if(g != previous_g + 1)
			{
				printf("Error, gates must be in sorted order, and full [0, 2^n - 1].");
			}
			previous_g = g;
			if(i != 1)
				C.circuit[i].gates[g] = gate(ty, u, v);
			else
			{
				assert(ty == 2 || ty == 3); 
				C.circuit[1].gates[g] = gate(4, g, 0);
				C.circuit[0].gates[g] = gate(ty, u, v);
			}
		}
		max_gate = previous_g;
		int cnt = 0;
		//2 while loop to find the next power of 2
		while(max_gate)
		{
			cnt++;
			max_gate >>= 1;

		}

		max_gate = 1;
		while(cnt)
		{
			max_gate <<= 1;
			cnt--;
			
		}
		int mx_gate = max_gate;
		while(mx_gate)
		{
			cnt++;
			mx_gate >>= 1;
		}
		if(n == 1)
		{
			//add a dummy gate to avoid ill-defined layer.
			if(i != 1)
			{
				C.circuit[i].gates[max_gate] = gate(2, 0, 0);
				C.circuit[i].bit_length = cnt;
			}
			else
			{
				C.circuit[0].gates[max_gate] = gate(2, 0, 0);
				C.circuit[0].bit_length = cnt;
				C.circuit[1].gates[max_gate] = gate(4, 1, 0);
				C.circuit[1].bit_length = cnt;
			}
		}
		else
		{
			C.circuit[i].bit_length = cnt - 1;
			if(i == 1)
				C.circuit[0].bit_length = cnt - 1;
		}
		fprintf(stderr, "layer %d, bit_length %d\n", i, C.circuit[i].bit_length);
		if(C.circuit[i].bit_length > max_bit_length)
			max_bit_length = C.circuit[i].bit_length;
	}
	p -> init_array(max_bit_length);

	beta_g_r0 = new prime_field::field_element[(1 << max_bit_length)];
	beta_g_r1 = new prime_field::field_element[(1 << max_bit_length)];
	beta_v = new prime_field::field_element[(1 << max_bit_length)];
	beta_u = new prime_field::field_element[(1 << max_bit_length)];
	fclose(circuit_in);
}

void verifier::read_circuit_from_string(char* file)
{
	int d;
	int offset;
	sscanf(file, "%d%n", &d, &offset);
	file += offset;
	int n;
	C.circuit = new layer[d];
	C.total_depth = d;
	int max_bit_length = -1;
	for(int i = 0; i < d; ++i)
	{
		sscanf(file, "%d%n", &n, &offset);
		file += offset;
		if(n == 1)
			C.circuit[i].gates = new gate[2];
		else
			C.circuit[i].gates = new gate[n];
		int max_gate = -1;
		int previous_g = -1;
		for(int j = 0; j < n; ++j)
		{
			int ty, g, u, v;
			sscanf(file, "%d%d%d%d%n", &ty, &g, &u, &v, &offset);
			file += offset;
			if(g != previous_g + 1)
			{
				printf("Error, gates must be in sorted order, and full [0, 2^n - 1].");
			}
			previous_g = g;
			C.circuit[i].gates[g] = gate(ty, u, v);
		}
		max_gate = previous_g;
		int cnt = 0;
		while(max_gate)
		{
			cnt++;
			max_gate >>= 1;
		}
		max_gate = 1;
		while(cnt)
		{
			max_gate <<= 1;
			cnt--;
		}
		int mx_gate = max_gate;
		while(mx_gate)
		{
			cnt++;
			mx_gate >>= 1;
		}
		if(n == 1)
		{
			//add a dummy gate to avoid ill-defined layer.
			C.circuit[i].gates[max_gate] = gate(2, 0, 0);
			C.circuit[i].bit_length = cnt;
		}
		else
		{
			C.circuit[i].bit_length = cnt - 1;
		}
		fprintf(stderr, "layer %d, bit_length %d\n", i, C.circuit[i].bit_length);
		if(C.circuit[i].bit_length > max_bit_length)
			max_bit_length = C.circuit[i].bit_length;
	}
	p -> init_array(max_bit_length);

	beta_g_r0 = new prime_field::field_element[(1 << max_bit_length)];
	beta_g_r1 = new prime_field::field_element[(1 << max_bit_length)];
	beta_v = new prime_field::field_element[(1 << max_bit_length)];
	beta_u = new prime_field::field_element[(1 << max_bit_length)];
}

prime_field::field_element verifier::add(int depth)
{
	//brute force for sanity check
	//it's slow
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 0)
		{
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	ret.value = ret.value % prime_field::mod;
	if(ret.value < 0)
		ret.value = ret.value + prime_field::mod;
	return ret;
}
prime_field::field_element verifier::mult(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 1)
		{
			//mpc
			// ret = ret + p->multiply(p->multiply((beta_g_r0[g] + beta_g_r1[g]),beta_u[u],p->prover_id),beta_v[v],p->prover_id);
			
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	ret.value = ret.value % prime_field::mod;
	if(ret.value < 0)
		ret.value = ret.value + prime_field::mod;
	return ret;
}

prime_field::field_element verifier::not_gate(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 6)
		{
			assert(v == 0);
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	return ret;
}

prime_field::field_element verifier::xor_gate(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 8)
		{
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	return ret;
}

prime_field::field_element verifier::minus_gate(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 7)
		{
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	ret.value = ret.value % prime_field::mod;
	if(ret.value < 0)
		ret.value = ret.value + prime_field::mod;
	return ret;
}

prime_field::field_element verifier::NAAB_gate(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 9)
		{
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * beta_u[u] * beta_v[v];
		}
	}
	ret.value = ret.value % prime_field::mod;
	if(ret.value < 0)
		ret.value = ret.value + prime_field::mod;
	return ret;
}

prime_field::field_element verifier::sum_gate(int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 5)
		{
			for(int j = u; j < v; ++j)
				ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * (beta_v[0]) * (beta_u[j]);
		}
	}
	ret.value = ret.value % prime_field::mod;
	if(ret.value < 0)
		ret.value = ret.value + prime_field::mod;
	return ret;
}

void verifier::beta_init(int depth, prime_field::field_element alpha, prime_field::field_element beta,
	const prime_field::field_element* r_0, const prime_field::field_element* r_1, 
	const prime_field::field_element* r_u, const prime_field::field_element* r_v, 
	const prime_field::field_element* one_minus_r_0, const prime_field::field_element* one_minus_r_1, 
	const prime_field::field_element* one_minus_r_u, const prime_field::field_element* one_minus_r_v)
{
	beta_g_r0[0] = alpha;
	beta_g_r1[0] = beta;
	for(int i = 0; i < C.circuit[depth].bit_length; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_g_r0[j | (1 << i)].value = beta_g_r0[j].value * r_0[i].value % prime_field::mod;
			beta_g_r1[j | (1 << i)].value = beta_g_r1[j].value * r_1[i].value % prime_field::mod;
		}
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_g_r0[j].value = beta_g_r0[j].value * one_minus_r_0[i].value % prime_field::mod;
			beta_g_r1[j].value = beta_g_r1[j].value * one_minus_r_1[i].value % prime_field::mod;
		}
	}
	beta_u[0] = prime_field::field_element(1);
	beta_v[0] = prime_field::field_element(1);
	for(int i = 0; i < C.circuit[depth - 1].bit_length; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_u[j | (1 << i)] = beta_u[j] * r_u[i];
			beta_v[j | (1 << i)] = beta_v[j] * r_v[i];
		}
			
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_u[j] = beta_u[j] * one_minus_r_u[i];
			beta_v[j] = beta_v[j] * one_minus_r_v[i];
		}
	}
}

prime_field::field_element verifier::direct_relay(int depth, prime_field::field_element *r_g, prime_field::field_element *r_u)
{
	if(depth != 1)
		return prime_field::field_element(0);
	else
	{
		prime_field::field_element ret = prime_field::field_element(1);
		for(int i = 0; i < C.circuit[depth].bit_length; ++i)
			ret = ret * (prime_field::field_element(1) - r_g[i] - r_u[i] + prime_field::field_element(2) * r_g[i] * r_u[i]);
		return ret;
	}
}

prime_field::field_element* generate_randomness(unsigned int size)
{
	int k = size;
	prime_field::field_element* ret;
	ret = new prime_field::field_element[k];

	for(int i = 0; i < k; ++i)
	{
	ret[i] = prime_field::random();
	ret[i] = prime_field::field_element(0);
	ret[i].value = ret[i].value % prime_field::mod;
	}
	return ret;
}

prime_field::field_element verifier::V_in(const prime_field::field_element* r_0, const prime_field::field_element* one_minus_r_0,
								prime_field::field_element* output_raw, int r_0_size, int output_size)
{
	prime_field::field_element* output = new prime_field::field_element[output_size];
	for(int i = 0; i < output_size; ++i)
		output[i] = output_raw[i];
	for(int i = 0; i < r_0_size; ++i)
	{
		for(int j = 0; j < (output_size >> 1); ++j)
			output[j] = output[j << 1] * (one_minus_r_0[i]) + output[j << 1 | 1] * (r_0[i]);
		output_size >>= 1;
	}
	auto ret = output[0];
	ret.value = ret.value % prime_field::mod;
	delete[] output;
	if(ret.value < 0)
		ret.value = ret.value + prime_field::mod;
	return ret;
}

prime_field::field_element verifier::relay_gate(const int depth)
{
	prime_field::field_element ret = prime_field::field_element(0);
	for(int i = 0; i < (1 << C.circuit[depth].bit_length); ++i)
	{
		int g = i, u = C.circuit[depth].gates[i].u, v = C.circuit[depth].gates[i].v;
		if(C.circuit[depth].gates[i].ty == 10)
		{
			assert(v == 0);
			ret = ret + (beta_g_r0[g] + beta_g_r1[g]) * (beta_u[u]) * (beta_v[v]);
		}
	}
	ret.value = ret.value % prime_field::mod;
	if(ret.value < 0)
		ret.value = ret.value + prime_field::mod;
	return ret;
}
bool verifier::verify_matrix()
{
	float proof_size = 0;
	auto result = p -> matrix_multiplication();
	

	prime_field::field_element *g,*h,*one_minus_g,*one_minus_h;
	bit_length = bit_length/2;
	one_minus_g = new prime_field::field_element[bit_length];
	one_minus_h = new prime_field::field_element[bit_length];

	g = generate_randomness(bit_length);
	h = generate_randomness(bit_length);

	for (int i = 0; i < (bit_length); ++i)
	{
		one_minus_g[i] = prime_field::field_element(1) - g[i];
		one_minus_h[i] = prime_field::field_element(1) - h[i];

	}	
	prime_field::field_element *gh,*one_minus_gh;
	gh = new prime_field::field_element[bit_length*2];
	one_minus_gh = new prime_field::field_element[bit_length*2];
	//merge randomness as well as one-minus randomness.
	for (int i = 0; i < (bit_length*2); ++i)
	{
		if(i<bit_length){
			gh[i] = g[i];
			one_minus_gh[i] = prime_field::field_element(1) - gh[i];
		}		
		else{
			gh[i] = h[i-bit_length];
			one_minus_gh[i] = prime_field::field_element(1) - gh[i];

		}
	}
	prime_field::field_element* result_flat = p -> result_flat;//linear verson of output matrix;



		// //mpc 
	int output_size = matrix_size*matrix_size;
	result_flat = p->merge_vector(result_flat,output_size);

	prime_field::field_element sum = p -> V_res(one_minus_gh, gh, result_flat, bit_length*2, (1<<(bit_length*2)));
	proof_size = proof_size + sizeof(sum);
	p->sumcheck_init_matrix(g,h,one_minus_g,one_minus_h);
	p->sumcheck_phase1_init_matrix();
	prime_field::field_element *r = generate_randomness(bit_length);
	prime_field::field_element previous_random = prime_field::field_element(0);
	for (int i = 0; i < (bit_length); ++i)
	{
		quadratic_poly poly = p -> sumcheck_phase1_update_matrix(previous_random, i);
		std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
		proof_size = proof_size + sizeof(poly);
		previous_random = r[i];

		if(poly.eval(0) + poly.eval(1)!=sum)
		{
			fprintf(stderr, "Sumcheck fail, current bit %d\n", i);
			cout<<sum.to_gmp_class()<<endl;
			cout<<(poly.eval(0) + poly.eval(1)).to_gmp_class()<<endl;
			return false;
		}
		else
		{
			// printf("Sumcheck pass round %d\n", i);
		}
		sum = poly.eval(r[i]);
		std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
		std::chrono::duration<double> t_v = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
		verifier_time += t_v.count();

	}
	cout<<"prover time: "<<p->total_time_matrix<<endl;


	return true;
}
bool verifier::verify()
{
	float proof_size = 0;
	prime_field::init_random();
	p -> proof_init();

	auto result = p -> evaluate();//This PART needs MPC

	prime_field::field_element alpha, beta;
	alpha.value = 1;
	beta.value = 0;
	random_oracle oracle;
	//initial random value
	

	prime_field::field_element *r_0 = generate_randomness(C.circuit[C.total_depth - 1].bit_length), *r_1 = generate_randomness(C.circuit[C.total_depth - 1].bit_length);
	prime_field::field_element *one_minus_r_0, *one_minus_r_1;
	one_minus_r_0 = new prime_field::field_element[C.circuit[C.total_depth - 1].bit_length];
	one_minus_r_1 = new prime_field::field_element[C.circuit[C.total_depth - 1].bit_length];

	for(int i = 0; i < (C.circuit[C.total_depth - 1].bit_length); ++i)
	{
		one_minus_r_0[i] = prime_field::field_element(1) - r_0[i];
		one_minus_r_1[i] = prime_field::field_element(1) - r_1[i];
	}
	
	// std::cerr << "Calc V_output(r)" << std::endl;
	

	int output_size = 1 << (C.circuit[C.total_depth - 1].bit_length);


	result = p->merge_vector(result,output_size);

	// for(int i = 0;i<output_size;i++){
	// 	cout<<result[i].to_gmp_class()<<endl;
	// }
	std::chrono::high_resolution_clock::time_point t_a = std::chrono::high_resolution_clock::now();
	prime_field::field_element a_0 = p -> V_res(one_minus_r_0, r_0, result, C.circuit[C.total_depth - 1].bit_length, (1 << (C.circuit[C.total_depth - 1].bit_length)));
	std::chrono::high_resolution_clock::time_point t_b = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> ts = std::chrono::duration_cast<std::chrono::duration<double>>(t_b - t_a);
	verifier_time += ts.count();

	a_0 = alpha * a_0;

	prime_field::field_element alpha_beta_sum = a_0; //+ a_1
	prime_field::field_element direct_relay_value;


	for(int i = C.total_depth - 1; i >= 1; --i)
	{
		std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
		// std::cerr << "Bound u start" << std::endl;
		p -> sumcheck_init(i, C.circuit[i].bit_length, C.circuit[i - 1].bit_length, C.circuit[i - 1].bit_length, alpha, beta, r_0, r_1, one_minus_r_0, one_minus_r_1);
		p -> sumcheck_phase1_init();
	
		prime_field::field_element previous_random = prime_field::field_element(0);
		//next level random
		auto r_u = generate_randomness(C.circuit[i - 1].bit_length);
		auto r_v = generate_randomness(C.circuit[i - 1].bit_length);
		direct_relay_value = alpha * direct_relay(i, r_0, r_u) + beta * direct_relay(i, r_1, r_u);
		prime_field::field_element *one_minus_r_u, *one_minus_r_v;
		one_minus_r_u = new prime_field::field_element[C.circuit[i - 1].bit_length];
		one_minus_r_v = new prime_field::field_element[C.circuit[i - 1].bit_length];
	
		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
		{
			one_minus_r_u[j] = prime_field::field_element(1) - r_u[j];
			one_minus_r_v[j] = prime_field::field_element(1) - r_v[j];
		}
		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
		{

			quadratic_poly poly = p -> sumcheck_phase1_update(previous_random, j);

			proof_size = proof_size + sizeof(poly);
			//merge poly from parties
			previous_random = r_u[j];
			std::chrono::high_resolution_clock::time_point t_v_phase1_start = std::chrono::high_resolution_clock::now();


			if(poly.eval(0) + poly.eval(1) != alpha_beta_sum)
			{
				fprintf(stderr, "Verification fail, phase1, circuit %d, current bit %d\n", i, j);
			
				cout<<(poly.eval(0) + poly.eval(1)).to_gmp_class()<<endl;
				cout<<alpha_beta_sum.to_gmp_class()<<endl;
				exit(1);
				return false;
			}
			else
			{
				fprintf(stderr, "Verification PASS, phase1, circuit %d, current bit %d\n", i, j);
			}
			alpha_beta_sum = poly.eval(r_u[j]);
			std::chrono::high_resolution_clock::time_point t_v_phase1_end = std::chrono::high_resolution_clock::now();
			std::chrono::duration<double> t_v_ph1 = std::chrono::duration_cast<std::chrono::duration<double>>(t_v_phase1_end - t_v_phase1_start);
			verifier_time += t_v_ph1.count();
			
		}

		std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

		std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
		// std::cerr << "	Time: " << time_span.count() << std::endl;
		
		// std::cerr << "Bound v start" << std::endl;
		t0 = std::chrono::high_resolution_clock::now();
		p -> sumcheck_phase2_init(previous_random, r_u, one_minus_r_u);
		previous_random = prime_field::field_element(0);
		cout<<(C.circuit[i - 1].bit_length)<<endl;
		for(int j = 0; j < C.circuit[i - 1].bit_length; ++j)
		{

			if(i == 1)
			r_v[j] = prime_field::field_element(0);
		
			quadratic_poly poly = p -> sumcheck_phase2_update(previous_random, j);
			std::chrono::high_resolution_clock::time_point t_v_phase2_start = std::chrono::high_resolution_clock::now();

			proof_size = proof_size + sizeof(poly);
			prime_field::field_element temp = p->merge(p->v_u);
			previous_random = r_v[j];
			if(poly.eval(0) + poly.eval(1) + direct_relay_value * temp != alpha_beta_sum)
			{
				fprintf(stderr, "Verification fail, phase2, circuit level %d, current bit %d\n", i, j);
				return false;
			}
			else
			{
				// fprintf(stderr, "Verification PASS, phase2, circuit level %d, current bit %d\n", i, j);

			}

			alpha_beta_sum = poly.eval(r_v[j]) + direct_relay_value * temp;
			std::chrono::high_resolution_clock::time_point t_v_phase2_end = std::chrono::high_resolution_clock::now();
			std::chrono::duration<double> t_v_ph2 = std::chrono::duration_cast<std::chrono::duration<double>>(t_v_phase2_end - t_v_phase2_start);
			verifier_time += t_v_ph2.count();
		}
			
		t1 = std::chrono::high_resolution_clock::now();
		time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
		// std::cerr << "	Time: " << time_span.count() << std::endl;
		
		auto final_claims = p -> sumcheck_finalize(previous_random);
		proof_size = proof_size + sizeof(final_claims);

		auto v_u = final_claims.first;
		auto v_v = final_claims.second;

		v_u = p->merge(v_u);
		v_v = p->merge(v_v);

		beta_init(i, alpha, beta, r_0, r_1, r_u, r_v, one_minus_r_0, one_minus_r_1, one_minus_r_u, one_minus_r_v);
		auto mult_value = mult(i);
		auto add_value = add(i);
		auto not_value = not_gate(i);
		auto minus_value = minus_gate(i);
		auto xor_value = xor_gate(i);
		auto naab_value = NAAB_gate(i);
		auto sum_value = sum_gate(i);
		auto relay_value = relay_gate(i);
		auto rhs = add_value * (v_u + v_v) + mult_value * v_u * v_v + direct_relay_value * v_u + not_value * (prime_field::field_element(1) - v_u) + minus_value * (v_u - v_v) + xor_value * (v_u + v_v - prime_field::field_element(2) * v_u * v_v) + naab_value * (v_v - v_u * v_v) + sum_value * v_u + relay_value * v_u;
		
		if(alpha_beta_sum != rhs)
		{
			fprintf(stderr, "Verification fail, semi final, circuit level %d\n", i);
			return false;
		}
		else
		{
			fprintf(stderr, "Verification PASS, semi final, circuit level %d\n", i);
		}
		auto tmp_alpha = generate_randomness(1), tmp_beta = generate_randomness(1);
		alpha = tmp_alpha[0];
		beta = tmp_beta[0];
		delete[] tmp_alpha;
		delete[] tmp_beta;
		if(i != 1)
			alpha_beta_sum = alpha * v_u + beta * v_v;
		else
		{
			alpha_beta_sum = v_u;
		}
		
		delete[] r_0;
		delete[] r_1;
		delete[] one_minus_r_0;
		delete[] one_minus_r_1;
		r_0 = r_u;
		r_1 = r_v;
		one_minus_r_0 = one_minus_r_u;
		one_minus_r_1 = one_minus_r_v;
		// std::cerr << "Prove Time " << p -> total_time << std::endl;
	}

	// cout<<"OUTPUT:"<<endl;
	// for(int i = 0;i<10;i++){
	// 	cout<<result[i].to_gmp_class()<<" ";
	// }
	// cout<<""<<endl;


	//post sumcheck
	prime_field::field_element* input;
	//prime_field::field_element* input2;
	input = new prime_field::field_element[(1 << C.circuit[0].bit_length)];
	//input2 = new prime_field::field_element[(1 << C.circuit[0].bit_length)];
	std::chrono::high_resolution_clock::time_point t_v_final_start = std::chrono::high_resolution_clock::now();

	for(int i = 0; i < (1 << C.circuit[0].bit_length); ++i)
	{
		int g = i;
		if(C.circuit[0].gates[g].ty == 3)
		{
			input[g] = prime_field::field_element(C.circuit[0].gates[g].u);
			// input[g] = prime_field::field_element(C.circuit[0].gates[g].u) - (p->rand);
			// input2[g] = p->rand;
		}
		else if(C.circuit[0].gates[g].ty == 2)
		{
			input[g] = prime_field::field_element(0);
			// input[g] = prime_field::field_element(C.circuit[0].gates[g].u) - (p->rand);
			// input2[g] = p->rand;


		}
		else
			assert(false);
	}
	auto input_0 = V_in(r_0, one_minus_r_0, input, C.circuit[0].bit_length, (1 << C.circuit[0].bit_length));
		// input_1 = V_in(r_1, one_minus_r_1, input, C.circuit[0].bit_length, (1 << C.circuit[0].bit_length));
	//auto input_0_2 = V_in(r_0, one_minus_r_0, input2, C.circuit[0].bit_length, (1 << C.circuit[0].bit_length));

	std::chrono::high_resolution_clock::time_point t_v_final_end = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> t_v_final = std::chrono::duration_cast<std::chrono::duration<double>>(t_v_final_end - t_v_final_start);
	verifier_time += t_v_final.count();

	delete[] input;
	delete[] r_0;
	delete[] r_1;
	delete[] one_minus_r_0;
	delete[] one_minus_r_1;

	if(alpha_beta_sum != input_0)
	{
		fprintf(stderr, "Verification fail, final input check fail.\n");
	
		return false;
	}
	else
	{
		fprintf(stderr, "Verification pass\n");
		std::cerr << "Prover total Time " << p -> total_time << std::endl;
		
		std::cerr << "Verifier Time " << verifier_time << std::endl;


	}
	// p->comm_size = p->comm_size + (p->Player_)->sent;
	// cout<<"Proof: "<<proof_size/1000<<" KB"<<endl;
	cout<<"Proof: "<<proof_size/1000.0<<" KB"<<endl;

	// if(p->prover_id==ALICE){
	// 	cout<<"Communication: "<<1702<<" MB"<<endl;
	// }else{
	// 	cout<<"Communication: "<<(p->comm_size)/1000000<<" MB"<<endl;
	// }

	p -> delete_self();
	delete_self();
	return true;
}

void verifier::delete_self()
{
	delete[] beta_g_r0;
	delete[] beta_g_r1;
	delete[] beta_u;
	delete[] beta_v;
	for(int i = 0; i < C.total_depth; ++i)
	{
		delete[] C.circuit[i].gates;
	}
	delete[] C.circuit;
}
