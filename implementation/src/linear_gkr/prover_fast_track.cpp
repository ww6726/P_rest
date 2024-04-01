#include "linear_gkr/prover_fast_track.h"
#include <iostream>
#include <fstream>
#include <unistd.h>
#include <sstream>
#include <vector>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <filesystem>
#include <dirent.h>
// client.cpp
#include <iostream>
#include <cstdlib>
#include <cstring>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

// #include <emp-sh2pc/emp-sh2pc.h>


#define MASK 4294967295 //2^32-1
#define PRIME 2305843009213693951 //2^61-1
typedef unsigned long long uint64;
#define ALICE 0
#define BOB 1
#define CAT 2
using namespace std;


uint64 myMod(uint64 x)
{
  return (x >> 61) + (x & PRIME);
}  
uint64 testAdd(uint64 x, uint64 y)
{
	return myMod(myMod(x) + myMod(y));
}
uint64 testMult(uint64 x, uint64 y)
{
	uint64 hi_x = x >> 32;
	uint64 hi_y = y >> 32;
	uint64 low_x = x & MASK;
	uint64 low_y = y & MASK;
	//since myMod might return something slightly large than 2^61-1,  
	//we need to multiply by 8 in two pieces to avoid overflow.
	uint64 piece1 = myMod((hi_x * hi_y)<< 3);
	uint64 z = (hi_x * low_y + hi_y * low_x);
	uint64 hi_z = z >> 32;
	uint64 low_z = z & MASK;

	//Note 2^64 mod (2^61-1) is 8
	uint64 piece2 = myMod((hi_z<<3) + myMod((low_z << 32)));
	uint64 piece3 = myMod(low_x * low_y);
	uint64 result = myMod(piece1 + piece2 + piece3);

	return result;

} 
void print_vector(prime_field::field_element* input, int size)
{
	for(int i =0;i<size;i++){
		cout<<input[i].to_gmp_class()<<" ";
	}
	cout<<""<<endl;
}
void print(prime_field::field_element input)
{
	cout<<input.to_gmp_class()<<endl;
}
void prover::get_circuit(const layered_circuit &from_verifier)
{
	C = from_verifier;
}
prime_field::field_element* twoD_to_1D(prime_field::field_element** input,int row,int col)
{
	prime_field::field_element* res = new prime_field::field_element[row*col];
	int idx = 0;
	for(int i = 0;i<row;i++){
		for(int j = 0;j<col;j++){
			res[idx++] = input[i][j];
		}	
	}
	return res;
}
prime_field::field_element** oneD_to_2D(prime_field::field_element* input,int size,int row,int col)
{
	prime_field::field_element** res = new prime_field::field_element*[row];
	int idx = 0;
	for(int i = 0;i<row;i++){
		res[i] = new prime_field::field_element[col];
		for(int j = 0;j<col;j++){
			res[i][j] = input[idx++];
		}	
	}
	return res;
}
void prover::get_matrices( prime_field::field_element** A_from_verifier, prime_field::field_element** B_from_verifier, int matrix_size_from_verifier)
{
	//MPC
	matrix_size = matrix_size_from_verifier;
	//split matrices into shares
	prime_field::field_element** matrix_rand = new prime_field::field_element*[matrix_size];
	prime_field::field_element** A_share_2 = new prime_field::field_element*[matrix_size];
	prime_field::field_element** B_share_2 = new prime_field::field_element*[matrix_size];

	for (int i = 0; i < matrix_size; ++i)
	{
		matrix_rand[i] = new prime_field::field_element[matrix_size];
		A_share_2[i] = new prime_field::field_element[matrix_size];
		B_share_2[i] = new prime_field::field_element[matrix_size];

		for (int j = 0; j < matrix_size; ++j)
		{
			matrix_rand[i][j] = 2;
			A_share_2[i][j] = A_from_verifier[i][j] - matrix_rand[i][j] - matrix_rand[i][j];
			B_share_2[i][j] = B_from_verifier[i][j] - matrix_rand[i][j] - matrix_rand[i][j];

		}
	}

	if(prover_id==ALICE){
		A = matrix_rand;
		B = matrix_rand;
	}else if(prover_id == BOB){
		A = matrix_rand;
		B = matrix_rand;
	}else{
		A = A_share_2;
		B = B_share_2;
	}
	

	// //single
	// matrix_size = matrix_size_from_verifier;
	// A = A_from_verifier;
	// B = B_from_verifier;

	// for(int i =0;i<matrix_size;i++){
	// 	for(int j =0;j<matrix_size;j++){
	// 		cout<<A[i][j].to_gmp_class()<<" ";
	// 	}
	// 	cout<<""<<endl;
	// }
	// 	cout<<"========================="<<endl;

	// for(int i =0;i<matrix_size;i++){
	// 	for(int j =0;j<matrix_size;j++){
	// 		cout<<B[i][j].to_gmp_class()<<" ";
	// 	}
	// 	cout<<""<<endl;
	// }

}
//fix this later
prime_field::field_element* prover::multiply(int size,prime_field::field_element* op1,prime_field::field_element* op2){
	prime_field::field_element* a = merge_vector_proof(op1,size);
	prime_field::field_element* b = merge_vector_proof(op2,size);

	prime_field::field_element* c = new prime_field::field_element[size];
	prime_field::field_element rand = 1;
	for(int i = 0;i <size;i++){
		prime_field::field_element each = a[i]*b[i];
		
		
		if(prover_id == ALICE){
			c[i] = rand;
		}else if(prover_id == BOB){
			c[i] = rand;
		}else{
			c[i] = each -rand - rand;
		}
	}
	return c;
}
prime_field::field_element prover::V_res(const prime_field::field_element* one_minus_r_0, const prime_field::field_element* r_0, const prime_field::field_element* output_raw, int r_0_size, int output_size)
{

	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	prime_field::field_element *output;
	output = new prime_field::field_element[output_size];
	for(int i = 0; i < output_size; ++i)
	{
		output[i] = output_raw[i];
	}
	for(int i = 0; i < r_0_size; ++i)
	{

		for(int j = 0; j < (output_size >> 1); ++j)
		{
			output[j].value = (output[j << 1].value * one_minus_r_0[i].value + output[j << 1 | 1].value * r_0[i].value) % prime_field::mod;
		}
		output_size >>= 1;
	}

	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
	total_time_matrix += time_span.count();

	prime_field::field_element res = output[0];
	delete[] output;

	if(res.value < 0)
		res.value = res.value + prime_field::mod;
	return res;
}
std::pair<std::vector<std::vector<prime_field::field_element>>, std::vector<prime_field::field_element>> prover::convolutionAsMatrixVector(const std::vector<std::vector<prime_field::field_element>>& input, 
	const std::vector<std::vector<prime_field::field_element>>& kernel, int inputHeight, int inputWidth, int kernelSize,int padding,int numInChannel) {
	// cout<<inputHeight<<" "<<inputWidth<<endl;
	// exit(1);
    int outputSize = (inputHeight - kernelSize + 1) * (inputWidth - kernelSize + 1);
    // std::vector<std::vector<std::vector<float>>> toeplitzMatrix(outputSize, std::vector<std::vector<float>>(kernelSize, std::vector<float>(kernelSize, 0.0)));
	std::vector<std::vector<prime_field::field_element>> toeplitzMatrix(outputSize, std::vector<prime_field::field_element>(kernelSize*kernelSize*numInChannel));

	for (int i = 0; i < outputSize; ++i) {
		int rowStart = i / (inputWidth - kernelSize + 1) * inputWidth + (i % (inputWidth - kernelSize + 1));
		int idx = 0;
		for (int j = 0; j < kernelSize * kernelSize; ++j) {
			int rowIndex = j / kernelSize;
			int colIndex = j % kernelSize;
			// toeplitzMatrix[i][rowIndex][colIndex] = input[rowStart + rowIndex * inputWidth + colIndex];

			for (int j = 0; j < numInChannel; j++)
			{
				toeplitzMatrix[i][idx+j*(kernelSize*kernelSize)] = input[rowStart + rowIndex * inputWidth + colIndex][j];
			}
			idx++;
		}
	}


    // Flatten the kernel
    std::vector<prime_field::field_element> flattenedKernel(kernelSize * kernelSize*numInChannel);

    for (int i = 0; i < kernelSize * kernelSize; ++i) {
		for (int j = 0; j < numInChannel; j++)
		{
        	flattenedKernel[i+j*(kernelSize*kernelSize)] = kernel[i][j];
		}
	}
	
	//return both matrix and kernel
	    return std::make_pair(toeplitzMatrix,flattenedKernel);
}
void prover::run_MPSPDZ(string mpspdz_dir,string compile_cmd,string run_cmd)
{
	//go to MPSPDZ
    chdir(mpspdz_dir.c_str());
	if(prover_id == ALICE){
		const char* compile_command = compile_cmd.c_str();
    	int compile_command_result = system(compile_command);
	}
	const char* run_command = run_cmd.c_str();
	int run_command_result = system(run_command);

	// string dir = "../Libra_single/implementation/tests/matmul";
	// chdir(dir.c_str());

	//return from MPSPDZ
	//no need actually
}
void send(prime_field::field_element share,string pipe_name){
	const char* pipeName = pipe_name.c_str();
	mkfifo(pipeName, 0666);
	// Open the named pipe for writing
	int pipeFd = open(pipeName, O_WRONLY);
	write(pipeFd, &share, sizeof(prime_field::field_element));
	close(pipeFd);
}
prime_field::field_element recv(string pipe_name)
{
	const char* pipeName = pipe_name.c_str();
	prime_field::field_element numberReceived;

	// Open the named pipe for reading
	int pipeFd = open(pipeName, O_RDONLY);

	// Read the number sent by the other process
	read(pipeFd, &numberReceived, sizeof(prime_field::field_element));
	
	// Close the pipe
	close(pipeFd);
	return numberReceived;

}
void send_data(prime_field::field_element data, int client)
{
    send(client, &data, sizeof(data), 0);
}
void send_datas(vector<prime_field::field_element>& data, int client)
{
    send(client, data.data(), sizeof(prime_field::field_element)*data.size(), 0);
}
prime_field::field_element recv_data(int client)
{
    prime_field::field_element received_data;
    recv(client, &received_data, sizeof(received_data), 0);
    return received_data;
}
vector<prime_field::field_element> recv_datas(int client, int n)
{	
    vector<prime_field::field_element> received_data(n);
    recv(client, received_data.data(), sizeof(prime_field::field_element)*n, 0);
    return received_data;
}
prime_field::field_element prover::merge_proof(prime_field::field_element share)
{	
	// // //inner-process
	// cout<<"merge_proof"<<endl;
	// string ab = "alice_bob";
	// string ac = "alice_cat";
	// string bc = "bob_cat";
	// prime_field::field_element share_merge;
	// if(prover_id==BOB){
	// 	send(share,ab);
	// 	share_merge = recv(bc);

	// }else if(prover_id==ALICE){
	// 	prime_field::field_element share_bob = recv(ab);
	// 	prime_field::field_element share_bob_alice = share + share_bob;
	// 	send(share_bob_alice,ac);
	// 	share_merge = recv(ac);

	// }else{
	// 	prime_field::field_element share_bob_alice = recv(ac);
	// 	share_merge = share + share_bob_alice;
	// 	send(share_merge,bc);
	// 	send(share_merge,ac);

	// }

	//network
	send_data(share, client);
	prime_field::field_element share_merge = recv_data(client);

	return share_merge;
}
prime_field::field_element* prover::merge_proofs(prime_field::field_element* share,int n)
{	
	vector<prime_field::field_element> shares(n);
	for(int i=0;i<n;i++){
		shares[i] = share[i];
	}

	send_datas(shares, client);
	auto res_merged = recv_datas(client,n);

	prime_field::field_element* share_merge = new prime_field::field_element[n];
	for(int i=0;i<n;i++){
		share_merge[i] = res_merged[i];
	}

	return share_merge;
}


prime_field::field_element prover::merge_WAN(prime_field::field_element share)
{
	 // Send and receive integers
    prime_field::field_element sentData = share;
    prime_field::field_element receivedData;

    // while (true) {
        if (send(clientSocket1, &sentData, sizeof(sentData), 0) == -1) {
            std::cerr << "Error sending data\n";
        }


        if (recv(clientSocket2, &receivedData, sizeof(receivedData), 0) == -1) {
            std::cerr << "Error receiving data\n";
        }
    // }

    return receivedData;
}
prime_field::field_element prover::merge(prime_field::field_element share)
{	

	prime_field::field_element* share_wrapper = new prime_field::field_element[1];
	share_wrapper[0] = share;
	feed_MPSPDZ_merge_input(share_wrapper,1);
	MPSPDZ_CMD cmd = MPSPDZ_CMD::merge;
	generate_MPSPDZ_cmd_and_run(cmd,1);
	prime_field::field_element* res = read_MPSPDZ_output(cmd,n);
	return res[0];
}
prime_field::field_element* prover::merge_vector_proof(prime_field::field_element* share, int n)
{
	prime_field::field_element* res = new prime_field::field_element[n];
	// for(int i =0;i<n;i++){
	// 	res[i] = merge_proof(share[i]);
	// }
	res = merge_proofs(share,n);
	return res;
}
prime_field::field_element* prover::merge_vector(prime_field::field_element* share, int n)
{

	feed_MPSPDZ_merge_input(share,n);
	MPSPDZ_CMD cmd = MPSPDZ_CMD::merge;
	generate_MPSPDZ_cmd_and_run(cmd,n);
	prime_field::field_element* res = read_MPSPDZ_output(cmd,n);
	return res;

	

}
prime_field::field_element* prover::read_MPSPDZ_output(MPSPDZ_CMD cmd,int size)
{
	prime_field::field_element* output_flat = new prime_field::field_element[size]; // Create a vector to store the numbers
	
	std::string line; // Temporary variable to read each line
	std::string word; // Temporary variable to extract each word
	string dir = "../../../../MP-SPDZ/";
    chdir(dir.c_str());

	string file_dir;
	if(prover_id == ALICE){
		file_dir += "Player-Data/Output_0";
	}else if(prover_id == BOB){
		file_dir += "Player-Data/Output_1";
	}else{
		file_dir += "Player-Data/Output_2";
	}
    std::ifstream outputFile(file_dir);
	// if (!outputFile) {
    //     std::cerr << "Failed to open the file." << std::endl;
    // }
	// int idx = 0;
	// prime_field::field_element zero(0);
	// prime_field::field_element neg = zero - 1;
	// while (std::getline(outputFile, line)) {
    //     std::istringstream iss(line); // Create a string stream for line
    //     while (iss >> word) { // Extract words separated by spaces
	// 		if(word[0]=='-'){
	// 			word = word.substr(1);
	// 			output_flat[idx++] = prime_field::field_element(word)*neg;
	// 		}else{
	// 			output_flat[idx++] = prime_field::field_element(word) - prime_field::mod;
	// 		}

    //     }
    // }
	// cout<<file_dir<<endl;

    // outputFile.close();
	// exit(1);
	std::string fileContents;

    if (outputFile.is_open()) {
        // Read the file into the string
        std::string line;
        while (std::getline(outputFile, line)) {
            fileContents += line + '\n'; // Add a newline character after each line
        }

        // Close the file
        outputFile.close();
    } else {
        std::cerr << "Failed to open the file." << std::endl;
    }
	prime_field::field_element zero(0);
	prime_field::field_element neg = zero - 1;
	std::string input = fileContents;
    std::vector<std::string> words;
    std::istringstream iss(input);
	int idx = 0;

    do {
        std::string word;
        iss >> word;
        if (!word.empty()) {
            if(word[0]=='-'){
				word = word.substr(1);
				output_flat[idx++] = prime_field::field_element(word)*neg;
			}else{
				output_flat[idx++] = prime_field::field_element(word);
			}
        }
    } while (iss);



	//split the output into shares
	if(cmd == MPSPDZ_CMD::matmul){
		prime_field::field_element rand = 1;
		if(prover_id== ALICE){
			for(int i =0;i<matrix_size*matrix_size;i++){
				output_flat[i] = rand;

			}
		}else if(prover_id== BOB){
			for(int i =0;i<matrix_size*matrix_size;i++){
				output_flat[i] =  rand;

			}
		}else{
			for(int i =0;i<matrix_size*matrix_size;i++){
				output_flat[i] = (output_flat[i]) - rand - rand;
			}
		}

	}else if(cmd == MPSPDZ_CMD::merge){
		
	}

	dir = "../Libra_single/implementation/tests/matmul";
	chdir(dir.c_str());



	return output_flat;


}
void prover::generate_MPSPDZ_cmd_and_run(MPSPDZ_CMD cmd_type, int merge_size)
{	string MPSPDZ_dir = "../../../../MP-SPDZ";
	string compile_cmd;
	string run_cmd;
	string matrix_size_str;
	string merge_size_str;
	// switch (cmd_type) {
    //     case MPSPDZ_CMD::matmul:
	// 		matrix_size_str = std::to_string(matrix_size);
	// 		compile_cmd = "./compile.py benchmark_matmul MATMUL " +matrix_size_str + " " + matrix_size_str + " " + "1 "+ matrix_size_str;
	// 		if(prover_id == ALICE){
	// 			run_cmd = "./lowgear-party.x -p 0 -N 3 -F -ip HOST benchmark_matmul-MATMUL-"+matrix_size_str+"-"+matrix_size_str+"-"+"1-"+matrix_size_str;
	// 		}else if(prover_id == BOB){
	// 			run_cmd = "./lowgear-party.x -p 1 -N 3 -F -ip HOST benchmark_matmul-MATMUL-"+matrix_size_str+"-"+matrix_size_str+"-"+"1-"+matrix_size_str;
	// 		}else{
	// 			run_cmd = "./lowgear-party.x -p 2 -N 3 -F -ip HOST benchmark_matmul-MATMUL-"+matrix_size_str+"-"+matrix_size_str+"-"+"1-"+matrix_size_str;
	// 		}
	// 		compile_cmd += " > /dev/null 2>&1";//run this without showing output
	// 		run_cmd += "> /dev/null 2>&1";//run this without showing output
    //         break;
    //     case MPSPDZ_CMD::merge:
	// 		 merge_size_str= std::to_string(merge_size);
	// 		compile_cmd = "./compile.py merge " +merge_size_str;
	// 		if(prover_id == ALICE){
	// 			run_cmd = "./lowgear-party.x -p 0 -N 3 -F -ip HOST merge-"+merge_size_str;
	// 		}else if(prover_id == BOB){
	// 			run_cmd = "./lowgear-party.x -p 1 -N 3 -F -ip HOST merge-"+merge_size_str;
	// 		}else{
	// 			run_cmd = "./lowgear-party.x -p 2 -N 3 -F -ip HOST merge-"+merge_size_str;
	// 		}
	// 		compile_cmd += " > /dev/null 2>&1";//run this without showing output
	// 		run_cmd += " > /dev/null 2>&1";//run this without showing output
    //         break;
        
    // }
	switch (cmd_type) {
        case MPSPDZ_CMD::matmul:
			matrix_size_str = std::to_string(matrix_size);
			compile_cmd = "python3 compile.py rescu_bench_vmatmult 1" +matrix_size_str;

			if(prover_id == ALICE){
				run_cmd = "./lowgear-party.x -p 0 -N 3 -F -ip HOST rescu_bench_vmatmult-1-"+matrix_size_str;

			}else if(prover_id == BOB){
				run_cmd = "./lowgear-party.x -p 1 -N 3 -F -ip HOST rescu_bench_vmatmult-1-"+matrix_size_str;

			}else{
				run_cmd = "./lowgear-party.x -p 2 -N 3 -F -ip HOST rescu_bench_vmatmult-1-"+matrix_size_str;

			}
			compile_cmd += " > /dev/null 2>&1";//run this without showing output
			run_cmd += "> /dev/null 2>&1";//run this without showing output
            break;
        case MPSPDZ_CMD::merge:
			 merge_size_str= std::to_string(merge_size);
			compile_cmd = "./compile.py merge " +merge_size_str;
			if(prover_id == ALICE){
				run_cmd = "./lowgear-party.x -p 0 -N 3 -F -ip HOST merge-"+merge_size_str;
			}else if(prover_id == BOB){
				run_cmd = "./lowgear-party.x -p 1 -N 3 -F -ip HOST merge-"+merge_size_str;
			}else{
				run_cmd = "./lowgear-party.x -p 2 -N 3 -F -ip HOST merge-"+merge_size_str;
			}
			compile_cmd += " > /dev/null 2>&1";//run this without showing output
			run_cmd += " > /dev/null 2>&1";//run this without showing output
            break;
    }

	run_MPSPDZ(MPSPDZ_dir,compile_cmd,run_cmd);
}
void prover::write_MPSDPZ_input_1D(string MPSPDZ_dir, string MPSPDZ_input_dir, prime_field::field_element* input_vector, int size){
    std::ofstream Player_input(MPSPDZ_input_dir);

	
	
    if (!Player_input) {
        std::cerr << "Error opening the file for writing." << std::endl;
		exit(1);
    }
    // Generate and write 1000 random numbers to the file with spaces between them
	for(int i =0;i<size;i++){
		
		Player_input << input_vector[i].to_gmp_class()<< " ";
	}
    // Close the file
    Player_input.close();

}
void prover::write_MPSDPZ_input_2D(string MPSPDZ_dir, string MPSPDZ_input_dir, prime_field::field_element** input_matrix){
    std::ofstream Player_input(MPSPDZ_input_dir);
	// char* cwd = getcwd( 0, 0 ) ; // **** microsoft specific ****
	// std::string working_directory(cwd) ;
	// std::free(cwd) ;
	// cout<<working_directory<<endl;

    if (!Player_input) {
        std::cerr << "Error opening the file for writing." << std::endl;
		exit(1);

    }
    // Generate and write 1000 random numbers to the file with spaces between them
	for(int i =0;i<matrix_size;i++){
		for(int j =0;j<matrix_size;j++){
			Player_input << input_matrix[i][j].to_gmp_class()<< " ";
		}
	}

    // Close the file
    Player_input.close();

}
void prover::feed_MPSPDZ_matmul_input(prime_field::field_element** A, prime_field::field_element** B)
{
	string MPSPDZ_dir = "../../../../MP-SPDZ";
	string MPSPDZ_input_dir = "../../../../MP-SPDZ/Player-Data/";
	if(prover_id == ALICE){
		MPSPDZ_input_dir += "Input-P0-0";
		write_MPSDPZ_input_2D(MPSPDZ_dir,MPSPDZ_input_dir,A);

	}else if(prover_id==BOB){
		MPSPDZ_input_dir += "Input-P1-0";
		write_MPSDPZ_input_2D(MPSPDZ_dir,MPSPDZ_input_dir,B);
	}
}
void prover::feed_MPSPDZ_merge_input(prime_field::field_element* input,int size)
{
	string MPSPDZ_dir = "../../../../MP-SPDZ";
	string MPSPDZ_input_dir = "../../../../MP-SPDZ/Player-Data/";
	if(prover_id == ALICE){
		MPSPDZ_input_dir += "Input-P0-0";
		write_MPSDPZ_input_1D(MPSPDZ_dir,MPSPDZ_input_dir,input,size);

	}else if(prover_id==BOB){
		MPSPDZ_input_dir += "Input-P1-0";
		write_MPSDPZ_input_1D(MPSPDZ_dir,MPSPDZ_input_dir,input,size);
	}else{
		MPSPDZ_input_dir += "Input-P2-0";
		write_MPSDPZ_input_1D(MPSPDZ_dir,MPSPDZ_input_dir,input,size);
	}
}
// prime_field::field_element** prover::matrix_multiplication()
// {

// }

prime_field::field_element* prover::matmul(prime_field::field_element** A, prime_field::field_element** B){
	//merge A, and merge B
	prime_field::field_element* A_flat = twoD_to_1D(A,matrix_size,matrix_size);
	prime_field::field_element* B_flat = twoD_to_1D(B,matrix_size,matrix_size);
	

	prime_field::field_element* A_merge_flat = merge_vector(A_flat,matrix_size*matrix_size);
	prime_field::field_element* B_merge_flat = merge_vector(B_flat,matrix_size*matrix_size);

	prime_field::field_element** A_merge = oneD_to_2D(A_merge_flat,matrix_size*matrix_size,matrix_size,matrix_size);
	prime_field::field_element** B_merge = oneD_to_2D(B_merge_flat,matrix_size*matrix_size,matrix_size,matrix_size);



	feed_MPSPDZ_matmul_input(A_merge,B_merge);
	MPSPDZ_CMD cmd = MPSPDZ_CMD::matmul;
	generate_MPSPDZ_cmd_and_run(cmd,0);
	return read_MPSPDZ_output(cmd,matrix_size*matrix_size);

}
prime_field::field_element** prover::matrix_multiplication()
{	

	//MPC
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	prime_field::field_element* result_flat_mpc = new prime_field::field_element[matrix_size*matrix_size];

	result_flat_mpc = matmul(A,B);
	int matrix_size_flat = matrix_size*matrix_size;
	print_vector(result_flat_mpc,matrix_size_flat);
	exit(1);
	
	// prime_field::field_element one(1);
	// merge_setup();

	// prime_field::field_element merged = merge_WAN(one);
	// cout<<merged.to_gmp_class()<<endl;
		// merge_WAN(one);
	// merge_WAN(one);

	prime_field::field_element** result_mpc = new prime_field::field_element*[matrix_size];
	int idx = 0;
	for (int i = 0; i < matrix_size; ++i)
	{
		result_mpc[i] = new prime_field::field_element[matrix_size];
		for (int j = 0; j < matrix_size; ++j)
		{
			result_mpc[i][j] = result_flat_mpc[idx++];
			// cout<<result_mpc[i][j].to_gmp_class()<<" ";
		}
		// cout<<""<<endl;
	}
	//SINGLE
	// prime_field::field_element** result = new prime_field::field_element*[matrix_size];
	// for (int i = 0; i < matrix_size; ++i)
	// {
	// 	result[i] = new prime_field::field_element[matrix_size];
	// 	for (int j = 0; j < matrix_size; ++j)
	// 	{
	// 		result[i][j] = 0;
	// 		for (int k = 0; k < matrix_size; ++k)
	// 		{
	// 			result[i][j] = result[i][j] + (A[i][k]*B[k][j]);
	// 		}
	// 	}
	// }
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	std::cerr << "matrix multiplication time: " << time_span.count() << " seconds." << std::endl;
	// std::chrono::high_resolution_clock::time_point t_table_initialize_t0 = std::chrono::high_resolution_clock::now();
	result_flat = new prime_field::field_element[matrix_size*matrix_size];
	for (int i = 0; i < matrix_size; ++i)
	{
		for (int j = 0; j < matrix_size; ++j)
		{
			A_poly[i*matrix_size+j] = A[i][j];
			B_poly[i*matrix_size+j] = B[i][j];
			C_poly[i*matrix_size+j] = result_mpc[i][j];
			result_flat[i*matrix_size+j] = result_mpc[i][j];
		}
	}
	result_flat = result_flat_mpc;
	// std::chrono::high_resolution_clock::time_point t_table_initialize_t1 = std::chrono::high_resolution_clock::now();
	// std::chrono::duration<double> time_span_table = std::chrono::duration_cast<std::chrono::duration<double>>(t_table_initialize_t1 - t_table_initialize_t0);
	// std::cerr << "Initialize bookkeeping table time: " << time_span_table.count() << " seconds." << std::endl;

	// //print output
	// cout<<"============A=============="<<endl;
	// for (int i = 0; i < matrix_size; ++i)
	// {
	// 	for (int j = 0; j < matrix_size; ++j)
	// 	{
	// 		cout<<A[i][j].to_gmp_class()<<" ";
	// 	}
	// 	cout<<""<<endl;
	// }
	// cout<<"============B=============="<<endl;
	// for (int i = 0; i < matrix_size; ++i)
	// {
	// 	for (int j = 0; j < matrix_size; ++j)
	// 	{
	// 		cout<<B[i][j].to_gmp_class()<<" ";
	// 	}
	// 	cout<<""<<endl;
	// }
	// cout<<"============C=============="<<endl;
	// for (int i = 0; i < matrix_size; ++i)
	// {
	// 	for (int j = 0; j < matrix_size; ++j)
	// 	{
	// 		cout<<result[i][j].to_gmp_class()<<" ";
	// 	}
	// 	cout<<""<<endl;
	// }
	// cout<<""<<endl;
	
	return result_mpc;
}
double* prover::do_something(){
	double* output = new double[10];
	output[0] = 23.4123;
	output[1] = -123.231;
	output[2] = 138.23;
	output[3] = 10.3248;
	output[4] = 89.2412;
	output[5] = -314.1234;
	output[6] = 823.2143;
	output[7] = -13.9473;
	output[8] = 59.3417;
	output[9] = -83.9507;
	return output;
}
prime_field::field_element* prover::evaluate()
{

	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	circuit_value[0] = new prime_field::field_element[(1 << C.circuit[0].bit_length)];
	prime_field::field_element rand = prime_field::field_element(2);

	for(int i = 0; i < (1 << C.circuit[0].bit_length); ++i)
	{
		int g, u, v, ty;
		g = i;
		u = C.circuit[0].gates[g].u;
		v = C.circuit[0].gates[g].v;
		ty = C.circuit[0].gates[g].ty;
		assert(ty == 3 || ty == 2);
		// //single
		// circuit_value[0][g] = prime_field::field_element(u);

		//3mpc
		// prime_field::field_element Share1 = rand;
		// prime_field::field_element Share2 = rand;
		// prime_field::field_element Share3= prime_field::field_element(u) - rand - rand;
        // if(prover_id==ALICE){//alice
        //     circuit_value[0][g] = Share1;

        // }else if(prover_id==BOB){//bob
        //     circuit_value[0][g] = Share2;

        // }
        // else{
        //     circuit_value[0][g] = Share3;
        // }

        //2mpc
        prime_field::field_element Share1 = rand;
        prime_field::field_element Share2 = rand;
        prime_field::field_element Share3 = prime_field::field_element(u) - rand - rand;

        if(prover_id==ALICE){
            circuit_value[0][g] = Share1;
        }
        else if(prover_id==BOB){
            circuit_value[0][g] = Share2;
        }else{
            circuit_value[0][g] = Share3;
		}
		
	}
	assert(C.total_depth < 1000000);
	for(int i = 1; i < C.total_depth; ++i)
	{
    
		circuit_value[i] = new prime_field::field_element[(1 << C.circuit[i].bit_length)];
		//initialize 2 arrays to store all the multiplication operands
		prime_field::field_element* op1 = new prime_field::field_element[1<<C.circuit[i].bit_length];
		prime_field::field_element* op2 = new prime_field::field_element[1<<C.circuit[i].bit_length];
		int* gate_idx = new int[1<<C.circuit[i].bit_length];
		int idx = 0;
        

        for(int j = 0; j < (1 << C.circuit[i].bit_length); ++j)
		{
			int g, u, v, ty;
			g = j;
			ty = C.circuit[i].gates[g].ty;
			u = C.circuit[i].gates[g].u;
			v = C.circuit[i].gates[g].v;
    		

            if(ty == 0)//ADD
			{
				circuit_value[i][g] = circuit_value[i - 1][u] + circuit_value[i - 1][v];
				
			}
			else if(ty == 1)//MULT
			{

				//mpc
				op1[idx] = circuit_value[i - 1][u];
				op2[idx] = circuit_value[i - 1][v];
				gate_idx[idx] = g;
				idx = idx+1;

				// prime_field::field_element* left = new prime_field::field_element[1];	
				// prime_field::field_element* right = new prime_field::field_element[1];	
				// left[0] = circuit_value[i - 1][u];
				// right[0] = circuit_value[i - 1][v];
				// prime_field::field_element res = multiply(1,left,right)[0];
				// circuit_value[i][g] = res;
				// cout<<merge(res).to_gmp_class()<<" ";
				// exit(1);

				// //single
				// circuit_value[i][g] = circuit_value[i - 1][u] * circuit_value[i - 1][v];

			}
			else if(ty == 2)//zero gate
			{				
				circuit_value[i][g] = prime_field::field_element(0);
			}
			else if(ty == 3)//input gate
			{
				circuit_value[i][g] = prime_field::field_element(u);
			}
			else if(ty == 4)//direct relay gate yes
			{
				circuit_value[i][g] = circuit_value[i - 1][u];
			}
			else if(ty == 5)//sum gate yes
			{
				circuit_value[i][g] = prime_field::field_element(0);
  				for(int k = u; k < v; ++k){
					circuit_value[i][g] = circuit_value[i][g] + circuit_value[i - 1][k];
				}
			
			}
			else if(ty == 6)//NOT gate
			{	
				circuit_value[i][g] = prime_field::field_element(1) - circuit_value[i - 1][u];
			}
			else if(ty == 7)//minus gate
			{
				circuit_value[i][g] = circuit_value[i - 1][u] - circuit_value[i - 1][v];
			}
			else if(ty == 8)//XOR gate
			{
				auto &x = circuit_value[i - 1][u], &y = circuit_value[i - 1][v];
				circuit_value[i][g] = x + y - prime_field::field_element(2) * x * y;
			}
			else if(ty == 9)//NAAB gate
			{
				auto &x = circuit_value[i - 1][u], &y = circuit_value[i - 1][v];
				circuit_value[i][g] = y - x * y;
			}
			else if(ty == 10)//relay
			{
				circuit_value[i][g] = circuit_value[i - 1][u];
			}
			else
			{
				assert(false);
			}
		}
		//here, batch multiply all the gates


		if(idx!=0){
			int size = idx;
			std::chrono::high_resolution_clock::time_point t_mul = std::chrono::high_resolution_clock::now();
			//method 2
			prime_field::field_element* res_per_layer = multiply(size, op1,op2);
	
			std::chrono::high_resolution_clock::time_point t_end_mul = std::chrono::high_resolution_clock::now();
			std::chrono::duration<double> ts_mul = std::chrono::duration_cast<std::chrono::duration<double>>(t_end_mul - t_mul);
			std::cerr << "	layer mul Time: " << ts_mul.count() << std::endl;

			for (int k = 0; k < size; k++)
			{
				int id = gate_idx[k];
				circuit_value[i][id] = res_per_layer[k];
			}
		}

	}
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
    if(prover_id==ALICE)
	   std::cerr << "total evaluation time: " << time_span.count() << " seconds." << std::endl;
	return circuit_value[C.total_depth - 1];
}
void prover::sumcheck_init_matrix(const prime_field::field_element* G, const prime_field::field_element* H,
	const prime_field::field_element* one_minus_G, const prime_field::field_element* one_minus_H)
{
	g = G;
	h = H;
	one_minus_g = one_minus_G;
	one_minus_h = one_minus_H;
	prime_field::field_element test;

}
void prover::sumcheck_init(int layer_id, int bit_length_g, int bit_length_u, int bit_length_v, 
	const prime_field::field_element &a, const prime_field::field_element &b, 
	const prime_field::field_element* R_0, const prime_field::field_element* R_1,
	prime_field::field_element* o_r_0, prime_field::field_element *o_r_1)
{
	r_0 = R_0;
	r_1 = R_1;
	alpha = a;
	beta = b;
	sumcheck_layer_id = layer_id;
	length_g = bit_length_g;
	length_u = bit_length_u;
	length_v = bit_length_v;
	one_minus_r_0 = o_r_0;
	one_minus_r_1 = o_r_1;
}
void prover::init_array_matrix(int max_bit_length)
{
	A_poly = new linear_poly[(1<<max_bit_length)];
	B_poly = new linear_poly[(1<<max_bit_length)];
	C_poly = new linear_poly[(1<<max_bit_length)];
	bit_length_matrix = max_bit_length;
	total_uv_matrix = 1<<(bit_length_matrix/2);
}

void prover::init_array(int max_bit_length)
{
	add_mult_sum = new linear_poly[(1 << max_bit_length)];
	V_mult_add = new linear_poly[(1 << max_bit_length)];
	addV_array = new linear_poly[(1 << max_bit_length)];
	beta_g_sum = new prime_field::field_element[(1 << max_bit_length)];
	beta_u = new prime_field::field_element[(1 << max_bit_length)];
	int half_length = (max_bit_length >> 1) + 1;
	beta_g_r0_fhalf = new prime_field::field_element[(1 << half_length)];
	beta_g_r0_shalf = new prime_field::field_element[(1 << half_length)];
	beta_g_r1_fhalf = new prime_field::field_element[(1 << half_length)];
	beta_g_r1_shalf = new prime_field::field_element[(1 << half_length)];
	beta_u_fhalf = new prime_field::field_element[(1 << half_length)];
	beta_u_shalf = new prime_field::field_element[(1 << half_length)];
}

void prover::delete_self()
{
	delete[] add_mult_sum;
	delete[] V_mult_add;
	delete[] addV_array;
	delete[] beta_u;
	delete[] beta_g_sum;

	delete[] beta_g_r0_fhalf;
	delete[] beta_g_r0_shalf;
	delete[] beta_g_r1_fhalf;
	delete[] beta_g_r1_shalf;
	delete[] beta_u_fhalf;
	delete[] beta_u_shalf;
	for(int i = 0; i < C.total_depth; ++i)
		delete[] circuit_value[i];
}
std::string toBinary(int n)
{
    std::string r;
    while(n!=0) {r=(n%2==0 ?"0":"1")+r; n/=2;}
    return r;
}
prover::~prover()
{
}
void prover::sumcheck_phase1_init_matrix()
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();

	int half_length = bit_length_matrix/2;
	int fl = bit_length_matrix;
	int l = half_length;
	for (int i = 0; i < l; ++i)
	{
		for (int b = 0; b < (1<<(fl-i-1)); ++b)
		{
			// cout<<toBinary(b)<<" "<<toBinary(b+(1<<(fl-i-1)))<<endl;
			 A_poly[b] = A_poly[b].b*one_minus_g[i] + A_poly[b + (1<<(fl-i-1))].b*g[i];
		}
	}

	for (int i = l-1; i >= 0; i--)
	{
		for (int b = 0; b < (1<<i); ++b)
		{
			for (int j = 0; j < (1<<l); ++j)
			{
			 // cout<<toBinary( b + (j*(1<<(i))))<<" "<<toBinary(b + (j*(1<<(i+1))))<<" "<<toBinary(b + (1<<i) + j*(1<<(i+1)))<<endl;
				B_poly[b+(j*(1<<i))].b = B_poly[b + (j*(1<<(i+1)))].b*one_minus_h[i] + B_poly[b + (1<<i) + j*(1<<(i+1))].b*h[i];
			}

			// B_poly[b].b = B_poly[(1<<(l-i))*b].b*one_minus_h[i] + B_poly[(1<<(l-i))*b + (1<<(l-i-1))].b*g[i];
		}
	}

	// cout<<"==============A=============="<<endl;
	// for (int i = 0; i < (1<<bit_length_matrix); ++i)
	// {
	// 	cout<<A_poly[i].b.to_gmp_class()<<" ";
	// }
	// cout<<""<<endl;
	// cout<<"==============B=============="<<endl;
	// for (int i = 0; i < (1<<bit_length_matrix); ++i)
	// {
	// 	cout<<B_poly[i].b.to_gmp_class()<<" ";
	// }
	// cout<<""<<endl;

	// cout<<"==============C=============="<<endl;
	// for (int i = 0; i < (1<<bit_length_matrix); ++i)
	// {
	// 	cout<<C_poly[i].b.to_gmp_class()<<" ";
	// }
	// cout<<""<<endl;
	// cout<<"============================"<<endl;

	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	double tmp = time_span.count();
	std::cerr << "Computing bookkeeping table time: " << time_span.count() << " seconds." << std::endl;

	total_time_matrix += time_span.count();
}

void prover::sumcheck_phase1_init()
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	//mult init
	total_uv = (1 << C.circuit[sumcheck_layer_id - 1].bit_length);
	prime_field::field_element zero = prime_field::field_element(0);

	for(int i = 0; i < total_uv; ++i)
	{
		V_mult_add[i] = circuit_value[sumcheck_layer_id - 1][i];//every poly's constant b is set to circuit value

		addV_array[i].a = zero;
		addV_array[i].b = zero;
		add_mult_sum[i].a = zero;
		add_mult_sum[i].b = zero;
	}
	beta_g_r0_fhalf[0] = alpha;
	beta_g_r1_fhalf[0] = beta;

	beta_g_r0_shalf[0] = prime_field::field_element(1);
	beta_g_r1_shalf[0] = prime_field::field_element(1);

	int first_half = length_g >> 1, second_half = length_g - first_half;
	//two for-loop to compute the polynomial G.
	for(int i = 0; i < first_half; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_g_r0_fhalf[j | (1 << i)].value = beta_g_r0_fhalf[j].value * r_0[i].value % prime_field::mod;
			beta_g_r0_fhalf[j].value = beta_g_r0_fhalf[j].value * one_minus_r_0[i].value % prime_field::mod;
			beta_g_r1_fhalf[j | (1 << i)].value = beta_g_r1_fhalf[j].value * r_1[i].value % prime_field::mod;
			beta_g_r1_fhalf[j].value = beta_g_r1_fhalf[j].value * one_minus_r_1[i].value % prime_field::mod;
		}
	}

	for(int i = 0; i < second_half; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_g_r0_shalf[j | (1 << i)].value = beta_g_r0_shalf[j].value * r_0[i + first_half].value % prime_field::mod;
			beta_g_r0_shalf[j].value = beta_g_r0_shalf[j].value * one_minus_r_0[i + first_half].value % prime_field::mod;
			beta_g_r1_shalf[j | (1 << i)].value = beta_g_r1_shalf[j].value * r_1[i + first_half].value % prime_field::mod;
			beta_g_r1_shalf[j].value = beta_g_r1_shalf[j].value * one_minus_r_1[i + first_half].value % prime_field::mod;
		}
	}

	int mask_fhalf = (1 << first_half) - 1;
	for(int i = 0; i < (1 << length_g); ++i)
	{
		beta_g_sum[i].value = (beta_g_r0_fhalf[i & mask_fhalf].value * beta_g_r0_shalf[i >> first_half].value 
							 + beta_g_r1_fhalf[i & mask_fhalf].value * beta_g_r1_shalf[i >> first_half].value) % prime_field::mod;
	}
	for(int i = 0; i < (1 << length_g); ++i)
	{
		int u, v;
		u = C.circuit[sumcheck_layer_id].gates[i].u;
		v = C.circuit[sumcheck_layer_id].gates[i].v;
		switch(C.circuit[sumcheck_layer_id].gates[i].ty)
		{
			case 0: //add gate
			{
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf].value * beta_g_r0_shalf[i >> first_half].value 
						+ beta_g_r1_fhalf[i & mask_fhalf].value * beta_g_r1_shalf[i >> first_half].value) % prime_field::mod;
				addV_array[u].b.value = (addV_array[u].b.value + circuit_value[sumcheck_layer_id - 1][v].value * tmp) % prime_field::mod;
				add_mult_sum[u].b.value = (add_mult_sum[u].b.value + tmp) % prime_field::mod;
				prime_field::field_element two(2);
				if(prover_id==ALICE){
					add_mult_sum[u].b = add_mult_sum[u].b - two - two;
					addV_array[u].b = addV_array[u].b - two - two;

				}else if(prover_id==BOB){
					add_mult_sum[u].b =  two;
					addV_array[u].b =  two;
				}else{
					add_mult_sum[u].b =  two;
					addV_array[u].b =  two;
				}
				break;
			}
			case 1: //mult gate
			{
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf].value * beta_g_r0_shalf[i >> first_half].value 
						+ beta_g_r1_fhalf[i & mask_fhalf].value * beta_g_r1_shalf[i >> first_half].value) % prime_field::mod;
				add_mult_sum[u].b.value = (add_mult_sum[u].b.value + circuit_value[sumcheck_layer_id - 1][v].value * tmp) % prime_field::mod;

				break;
			}
			case 4: //direct relay gate
			{
				auto tmp = (beta_g_r0_fhalf[u & mask_fhalf].value * beta_g_r0_shalf[u >> first_half].value 
						+ beta_g_r1_fhalf[u & mask_fhalf].value * beta_g_r1_shalf[u >> first_half].value) % prime_field::mod;
				
				prime_field::field_element temp;
				temp.value = tmp;

				add_mult_sum[u].b.value = (add_mult_sum[u].b.value + tmp) % prime_field::mod;
				prime_field::field_element two(2);
				if(prover_id==ALICE){
					add_mult_sum[u].b = add_mult_sum[u].b - two - two;

				}else if(prover_id==BOB){
					add_mult_sum[u].b =  two;

				}else{
					add_mult_sum[u].b =  two;

				}

				break;
			}
			case 5: //sum gate
			{
				auto tmp = beta_g_r0_fhalf[i & mask_fhalf].value * beta_g_r0_shalf[i >> first_half].value 
					+ beta_g_r1_fhalf[i & mask_fhalf].value * beta_g_r1_shalf[i >> first_half].value;
				tmp = tmp % prime_field::mod;
				for(int j = u; j < v; ++j)
				{
					add_mult_sum[j].b.value = (add_mult_sum[j].b.value + tmp); 
					if(add_mult_sum[j].b.value >= prime_field::mod)
						add_mult_sum[j].b.value = add_mult_sum[j].b.value - prime_field::mod;
			
					prime_field::field_element two(2);
					if(prover_id==ALICE){
						add_mult_sum[j].b = add_mult_sum[j].b - two -two;

					}else if(prover_id==BOB){
						add_mult_sum[j].b =  two;

					}else{
						add_mult_sum[j].b =  two;
					}
				}
				break;
			}
			case 6: //NOT gate
			{
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf].value * beta_g_r0_shalf[i >> first_half].value 
						+ beta_g_r1_fhalf[i & mask_fhalf].value * beta_g_r1_shalf[i >> first_half].value) % prime_field::mod;
				add_mult_sum[u].b.value = (add_mult_sum[u].b.value + prime_field::mod - tmp) % prime_field::mod;
				addV_array[u].b.value = (addV_array[u].b.value + tmp) % prime_field::mod;
				break;
			}
			case 7: //minus gate
			{
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf].value * beta_g_r0_shalf[i >> first_half].value 
						+ beta_g_r1_fhalf[i & mask_fhalf].value * beta_g_r1_shalf[i >> first_half].value) % prime_field::mod;
				addV_array[u].b.value = (addV_array[u].b.value + prime_field::mod - (circuit_value[sumcheck_layer_id - 1][v].value * tmp % prime_field::mod)) % prime_field::mod;
				add_mult_sum[u].b.value = (add_mult_sum[u].b.value + tmp) % prime_field::mod;
				break;
			}
			case 8: //XOR gate
			{
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf].value * beta_g_r0_shalf[i >> first_half].value 
						+ beta_g_r1_fhalf[i & mask_fhalf].value * beta_g_r1_shalf[i >> first_half].value) % prime_field::mod;
				addV_array[u].b.value = (addV_array[u].b.value + tmp * circuit_value[sumcheck_layer_id - 1][v].value % prime_field::mod) % prime_field::mod;
				add_mult_sum[u].b.value = (add_mult_sum[u].b.value + tmp + prime_field::mod - (prime_field::field_element(2).value * circuit_value[sumcheck_layer_id - 1][v].value % prime_field::mod * tmp % prime_field::mod)) % prime_field::mod;
				break;
			}
			case 9: //NAAB gate
			{
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf].value * beta_g_r0_shalf[i >> first_half].value 
						+ beta_g_r1_fhalf[i & mask_fhalf].value * beta_g_r1_shalf[i >> first_half].value) % prime_field::mod;
				addV_array[u].b.value = (addV_array[u].b.value + tmp * circuit_value[sumcheck_layer_id - 1][v].value % prime_field::mod) % prime_field::mod;
				add_mult_sum[u].b.value = (add_mult_sum[u].b.value + prime_field::mod - (circuit_value[sumcheck_layer_id - 1][v].value * tmp % prime_field::mod)) % prime_field::mod;
				break;
			}
			case 10: //relay gate
			{
				auto tmp = (beta_g_r0_fhalf[i & mask_fhalf].value * beta_g_r0_shalf[i >> first_half].value 
						+ beta_g_r1_fhalf[i & mask_fhalf].value * beta_g_r1_shalf[i >> first_half].value) % prime_field::mod;
				add_mult_sum[u].b.value = (add_mult_sum[u].b.value + tmp) % prime_field::mod;
				break;
			}
			default:
			{
				break;
			}
		}
	}

	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	double tmp = time_span.count();
	total_time += time_span.count();
}
quadratic_poly prover::sumcheck_phase1_update_matrix(prime_field::field_element previous_random, int current_bit)
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	quadratic_poly ret = quadratic_poly(prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0));
	prime_field::field_element* A_a = new prime_field::field_element[total_uv_matrix>>1];
	prime_field::field_element* A_b = new prime_field::field_element[total_uv_matrix>>1];
	prime_field::field_element* B_a = new prime_field::field_element[total_uv_matrix>>1];
	prime_field::field_element* B_b = new prime_field::field_element[total_uv_matrix>>1];

	int size = total_uv_matrix>>1;

	for (int i = 0; i < (total_uv_matrix>>1); ++i)
	{
		int g_zero = i << 1, g_one = i << 1 | 1;//even and odd
		if(current_bit==0)
		{
			A_poly[i].b = A_poly[g_zero].b;
			A_poly[i].a = A_poly[g_one].b - A_poly[i].b; 

			B_poly[i].b = B_poly[g_zero].b;
			B_poly[i].a = B_poly[g_one].b - B_poly[i].b; 
		}
		else
		{
			A_poly[i].b.value = (A_poly[g_zero].a.value * previous_random.value + A_poly[g_zero].b.value) % prime_field::mod;
			A_poly[i].a.value = (A_poly[g_one].a.value * previous_random.value + A_poly[g_one].b.value - A_poly[i].b.value + prime_field::mod) % prime_field::mod;

			B_poly[i].b.value = (B_poly[g_zero].a.value * previous_random.value + B_poly[g_zero].b.value) % prime_field::mod;
			B_poly[i].a.value = (B_poly[g_one].a.value * previous_random.value + B_poly[g_one].b.value - B_poly[i].b.value + prime_field::mod) % prime_field::mod;

		}
	

		// //single
		// ret.a = (ret.a + A_poly[i].a * B_poly[i].a);
		// ret.b = (ret.b + A_poly[i].a * B_poly[i].b + A_poly[i].b * B_poly[i].a);
		// ret.c = (ret.c + A_poly[i].b * B_poly[i].b);

		//mpc
		A_a[i] = A_poly[i].a;
		A_b[i] = A_poly[i].b;

		B_a[i] = B_poly[i].a;
		B_b[i] = B_poly[i].b;

	}

	//==============mpc===================
	prime_field::field_element* coeff_a = multiply(size,A_a, B_a);
	prime_field::field_element* coeff_b_l = multiply(size,A_a, B_b);
	prime_field::field_element* coeff_b_r = multiply(size,A_b, B_a);
	prime_field::field_element* coeff_c = multiply(size,A_b, B_b);
	prime_field::field_element test_a(0);
	prime_field::field_element test_b(0);
	prime_field::field_element test_c(0);
	for (int i = 0; i < size; i++)
	{
		test_a = test_a + coeff_a[i];
		test_b = test_b + coeff_b_l[i] + coeff_b_r[i];
		test_c = test_c + coeff_c[i];

	}


	test_a.value = test_a.value% prime_field::mod;
	test_b.value = test_b.value% prime_field::mod;
	test_c.value = test_c.value% prime_field::mod;

	ret.a = test_a;
	ret.b = test_b;
	ret.c = test_c;

	//merge the result
	prime_field::field_element* combine_merge = new prime_field::field_element[3];
	combine_merge[0] = ret.a;
	combine_merge[1] = ret.b;
	combine_merge[2] = ret.c;
	prime_field::field_element* ret_all = merge_vector(combine_merge,3);

	ret.a =  ret_all[0];
	ret.b =  ret_all[1];
	ret.c =  ret_all[2];

	//==============mpc===================

	total_uv_matrix >>= 1;
	ret.a.value = ret.a.value % prime_field::mod;
	ret.b.value = ret.b.value % prime_field::mod;
	ret.c.value = ret.c.value % prime_field::mod;
	
	ret.a.value = (ret.a.value + prime_field::mod) % prime_field::mod;
	ret.b.value = (ret.b.value + prime_field::mod) % prime_field::mod;
	ret.c.value = (ret.c.value + prime_field::mod) % prime_field::mod;


	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	double tmp = time_span.count();
	total_time_matrix += time_span.count();
	return ret;
}
quadratic_poly prover::sumcheck_phase1_update(prime_field::field_element previous_random, int current_bit)
{
	prime_field::field_element* add_mult_sum_a = new prime_field::field_element[total_uv >> 1];
	prime_field::field_element* add_mult_sum_b = new prime_field::field_element[total_uv >> 1];

	prime_field::field_element* V_mult_add_a = new prime_field::field_element[total_uv >> 1];
	prime_field::field_element* V_mult_add_b = new prime_field::field_element[total_uv >> 1];

	prime_field::field_element* addV_array_a = new prime_field::field_element[total_uv >> 1];
	prime_field::field_element* addV_array_b = new prime_field::field_element[total_uv >> 1];

	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	quadratic_poly ret = quadratic_poly(prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0));


	int size = total_uv >> 1;
	for(int i = 0; i < (total_uv >> 1); ++i)
	{
		prime_field::field_element zero_value, one_value;
		int g_zero = i << 1, g_one = i << 1 | 1;//even and odd
		if(current_bit == 0)
		{
			V_mult_add[i].b = V_mult_add[g_zero].b;
			V_mult_add[i].a = V_mult_add[g_one].b - V_mult_add[i].b;

			addV_array[i].b = addV_array[g_zero].b;
			addV_array[i].a = addV_array[g_one].b - addV_array[i].b;


			add_mult_sum[i].b = add_mult_sum[g_zero].b;
			add_mult_sum[i].a = add_mult_sum[g_one].b - add_mult_sum[i].b;

	
		}
		else
		{

			V_mult_add[i].b.value = (V_mult_add[g_zero].a.value * previous_random.value + V_mult_add[g_zero].b.value) % prime_field::mod;
			V_mult_add[i].a.value = (V_mult_add[g_one].a.value * previous_random.value + V_mult_add[g_one].b.value - V_mult_add[i].b.value + prime_field::mod) % prime_field::mod;

			addV_array[i].b.value = (addV_array[g_zero].a.value * previous_random.value + addV_array[g_zero].b.value) % prime_field::mod;
			addV_array[i].a.value = (addV_array[g_one].a.value * previous_random.value + addV_array[g_one].b.value - addV_array[i].b.value + prime_field::mod) % prime_field::mod;

			add_mult_sum[i].b.value = (add_mult_sum[g_zero].a.value * previous_random.value + add_mult_sum[g_zero].b.value) % prime_field::mod;
			add_mult_sum[i].a.value = (add_mult_sum[g_one].a.value * previous_random.value + add_mult_sum[g_one].b.value - add_mult_sum[i].b.value + prime_field::mod) % prime_field::mod;

		}

		

		// //single
		// ret.a.value = (ret.a.value + add_mult_sum[i].a.value * V_mult_add[i].a.value) % prime_field::mod;
		// ret.b.value = (ret.b.value + add_mult_sum[i].a.value * V_mult_add[i].b.value + add_mult_sum[i].b.value * V_mult_add[i].a.value
		// 							+ addV_array[i].a.value) % prime_field::mod;
		// ret.c.value = (ret.c.value + add_mult_sum[i].b.value * V_mult_add[i].b.value
		// 							+ addV_array[i].b.value) % prime_field::mod;

		//vectorized mpc
		add_mult_sum_a[i] = add_mult_sum[i].a; 
		add_mult_sum_b[i] = add_mult_sum[i].b; 
		V_mult_add_a[i] = V_mult_add[i].a; 
		V_mult_add_b[i] = V_mult_add[i].b; 


	}

		// prime_field::field_element* res = mpc_product<Share<gfp_<0, 4>>>(prover_id, 2, 254,num_op,op1,op2);

	//vectorized mpc
	std::chrono::high_resolution_clock::time_point t_mpc_start = std::chrono::high_resolution_clock::now();
	// prime_field::field_element* coeff_a = mpc_product_no_setup(&P,set,prover_id,size,add_mult_sum_a,V_mult_add_a);
	// prime_field::field_element* coeff_b_l = mpc_product_no_setup(&P,set,prover_id,size,add_mult_sum_a,V_mult_add_b);
	// prime_field::field_element* coeff_b_r = mpc_product_no_setup(&P,set,prover_id,size,add_mult_sum_b,V_mult_add_a);
	// prime_field::field_element* coeff_c = mpc_product_no_setup(&P,set,prover_id,size,add_mult_sum_b,V_mult_add_b);

	prime_field::field_element* coeff_a = multiply(size,add_mult_sum_a,V_mult_add_a);
	prime_field::field_element* coeff_b_l = multiply(size,add_mult_sum_a,V_mult_add_b);
	prime_field::field_element* coeff_b_r = multiply(size,add_mult_sum_b,V_mult_add_a);
	prime_field::field_element* coeff_c = multiply(size,add_mult_sum_b,V_mult_add_b);


	std::chrono::high_resolution_clock::time_point t_mpc_end = std::chrono::high_resolution_clock::now();
	std::chrono::duration<double> time_mpc = std::chrono::duration_cast<std::chrono::duration<double>>(t_mpc_end - t_mpc_start);
	// std::cerr << "phase 1 mpc time: " << time_mpc.count() << " seconds." << std::endl;

	prime_field::field_element test_a(0);
	prime_field::field_element test_b(0);
	prime_field::field_element test_c(0);

	for (int i = 0; i < size; i++)
	{
		test_a = test_a + coeff_a[i];
		test_b = test_b + coeff_b_l[i] + coeff_b_r[i];
		test_c = test_c + coeff_c[i] + addV_array[i].b;

	}


	test_a.value = test_a.value% prime_field::mod;
	test_b.value = test_b.value% prime_field::mod;
	test_c.value = test_c.value% prime_field::mod;


	ret.a = test_a;
	ret.b = test_b;
	ret.c = test_c;

	//merge the result
	ret.a =  merge(ret.a);
	ret.b =  merge(ret.b);
	ret.c =  merge(ret.c);

	

	total_uv >>= 1;
	ret.a.value = ret.a.value % prime_field::mod;
	ret.b.value = ret.b.value % prime_field::mod;
	ret.c.value = ret.c.value % prime_field::mod;
	
	ret.a.value = (ret.a.value + prime_field::mod) % prime_field::mod;
	ret.b.value = (ret.b.value + prime_field::mod) % prime_field::mod;
	ret.c.value = (ret.c.value + prime_field::mod) % prime_field::mod;
	

	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();


	return ret;
}

void prover::sumcheck_phase2_init(prime_field::field_element previous_random, const prime_field::field_element* r_u, const prime_field::field_element* one_minus_r_u)
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	v_u = V_mult_add[0].eval(previous_random);

	int first_half = length_u >> 1, second_half = length_u - first_half;

	beta_u_fhalf[0] = prime_field::field_element(1);
	beta_u_shalf[0] = prime_field::field_element(1);
	for(int i = 0; i < first_half; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_u_fhalf[j | (1 << i)].value = beta_u_fhalf[j].value * r_u[i].value % prime_field::mod;
			beta_u_fhalf[j].value = beta_u_fhalf[j].value * one_minus_r_u[i].value % prime_field::mod;
		}
	}

	for(int i = 0; i < second_half; ++i)
	{
		for(int j = 0; j < (1 << i); ++j)
		{
			beta_u_shalf[j | (1 << i)].value = beta_u_shalf[j].value * r_u[i + first_half].value % prime_field::mod;
			beta_u_shalf[j].value = beta_u_shalf[j].value * one_minus_r_u[i + first_half].value % prime_field::mod;
		}
	}

	int mask_fhalf = (1 << first_half) - 1;
	for(int i = 0; i < (1 << length_u); ++i)
	{
		beta_u[i].value = beta_u_fhalf[i & mask_fhalf].value * beta_u_shalf[i >> first_half].value % prime_field::mod;
	}

	
	total_uv = (1 << C.circuit[sumcheck_layer_id - 1].bit_length);
	int total_g = (1 << C.circuit[sumcheck_layer_id].bit_length);
	prime_field::field_element zero = prime_field::field_element(0);
	for(int i = 0; i < total_uv; ++i)
	{
		add_mult_sum[i].a = zero;
		add_mult_sum[i].b = zero;
		addV_array[i].a = zero;
		addV_array[i].b = zero;
		V_mult_add[i] = circuit_value[sumcheck_layer_id - 1][i];
	}
	int first_g_half = (length_g >> 1);
	int mask_g_fhalf = (1 << (length_g >> 1)) - 1;
	for(int i = 0; i < total_g; ++i)
	{
		int ty = C.circuit[sumcheck_layer_id].gates[i].ty;
		int u = C.circuit[sumcheck_layer_id].gates[i].u;
		int v = C.circuit[sumcheck_layer_id].gates[i].v;
		switch(ty)
		{
			case 1: //mult gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf].value * beta_u_shalf[u >> first_half].value % prime_field::mod;
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf].value * beta_g_r0_shalf[i >> first_g_half].value 
								+ beta_g_r1_fhalf[i & mask_g_fhalf].value * beta_g_r1_shalf[i >> first_g_half].value) % prime_field::mod;
				add_mult_sum[v].b.value = add_mult_sum[v].b.value + (tmp_g * tmp_u % prime_field::mod * v_u.value);
				add_mult_sum[v].b.value = add_mult_sum[v].b.value % prime_field::mod;
				break;
			}
			case 0: //add gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf].value * beta_u_shalf[u >> first_half].value % prime_field::mod;
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf].value * beta_g_r0_shalf[i >> first_g_half].value 
								+ beta_g_r1_fhalf[i & mask_g_fhalf].value * beta_g_r1_shalf[i >> first_g_half].value) % prime_field::mod;
				add_mult_sum[v].b.value = (add_mult_sum[v].b.value + tmp_g * tmp_u);
				addV_array[v].b.value = ((tmp_g * tmp_u % prime_field::mod) * v_u.value + addV_array[v].b.value);

				add_mult_sum[v].b.value = add_mult_sum[v].b.value % prime_field::mod;
				addV_array[v].b.value = addV_array[v].b.value % prime_field::mod;
				break;
			}
			case 5: //sum gate
			{
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf].value * beta_g_r0_shalf[i >> first_g_half].value 
							+ beta_g_r1_fhalf[i & mask_g_fhalf].value * beta_g_r1_shalf[i >> first_g_half].value) % prime_field::mod;
				auto tmp_g_vu = tmp_g * v_u.value % prime_field::mod;
				for(int j = u; j < v; ++j)
				{
					auto tmp_u = beta_u_fhalf[j & mask_fhalf].value * beta_u_shalf[j >> first_half].value % prime_field::mod;
					addV_array[0].b.value = (addV_array[0].b.value + tmp_g_vu * tmp_u) % prime_field::mod;
				}
				break;
			}
			case 6: //not gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf].value * beta_u_shalf[u >> first_half].value % prime_field::mod;
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf].value * beta_g_r0_shalf[i >> first_g_half].value 
								+ beta_g_r1_fhalf[i & mask_g_fhalf].value * beta_g_r1_shalf[i >> first_g_half].value) % prime_field::mod;
				addV_array[v].b.value = (addV_array[v].b.value + tmp_g * tmp_u % prime_field::mod + prime_field::mod - tmp_g * tmp_u % prime_field::mod * v_u.value % prime_field::mod) % prime_field::mod;
				break;
			}
			case 7: //minus gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf].value * beta_u_shalf[u >> first_half].value % prime_field::mod;
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf].value * beta_g_r0_shalf[i >> first_g_half].value 
								+ beta_g_r1_fhalf[i & mask_g_fhalf].value * beta_g_r1_shalf[i >> first_g_half].value) % prime_field::mod;
				add_mult_sum[v].b.value = (add_mult_sum[v].b.value + prime_field::mod - tmp_g * tmp_u % prime_field::mod) % prime_field::mod;
				addV_array[v].b.value = ((tmp_g * tmp_u % prime_field::mod) * v_u.value + addV_array[v].b.value) % prime_field::mod;
				break;
			}
			case 8: //xor gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf].value * beta_u_shalf[u >> first_half].value % prime_field::mod;
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf].value * beta_g_r0_shalf[i >> first_g_half].value 
								+ beta_g_r1_fhalf[i & mask_g_fhalf].value * beta_g_r1_shalf[i >> first_g_half].value) % prime_field::mod;
				auto tmp = tmp_g * tmp_u % prime_field::mod;
				add_mult_sum[v].b.value = (add_mult_sum[v].b.value + tmp + prime_field::mod - (prime_field::field_element(2).value * v_u.value) % prime_field::mod * tmp % prime_field::mod) % prime_field::mod;
				addV_array[v].b.value = (addV_array[v].b.value + tmp * v_u.value % prime_field::mod) % prime_field::mod;
				break;
			}
			case 9: //NAAB gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf].value * beta_u_shalf[u >> first_half].value % prime_field::mod;
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf].value * beta_g_r0_shalf[i >> first_g_half].value 
								+ beta_g_r1_fhalf[i & mask_g_fhalf].value * beta_g_r1_shalf[i >> first_g_half].value) % prime_field::mod;
				auto tmp = tmp_g * tmp_u % prime_field::mod;
				add_mult_sum[v].b.value = (add_mult_sum[v].b.value + tmp + prime_field::mod - v_u.value * tmp % prime_field::mod) % prime_field::mod;
				break;
			}
			case 10: //relay gate
			{
				auto tmp_u = beta_u_fhalf[u & mask_fhalf].value * beta_u_shalf[u >> first_half].value % prime_field::mod;
				auto tmp_g = (beta_g_r0_fhalf[i & mask_g_fhalf].value * beta_g_r0_shalf[i >> first_g_half].value 
								+ beta_g_r1_fhalf[i & mask_g_fhalf].value * beta_g_r1_shalf[i >> first_g_half].value) % prime_field::mod;
				auto tmp = tmp_g * tmp_u % prime_field::mod;
				addV_array[v].b.value = (addV_array[v].b.value + tmp * v_u.value) % prime_field::mod;
				assert(v == 0);
				break;
			}
			default:
			{
				break;
			}
		}
	}

	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();
}

quadratic_poly prover::sumcheck_phase2_update(prime_field::field_element previous_random, int current_bit)
{
	std::chrono::high_resolution_clock::time_point t0 = std::chrono::high_resolution_clock::now();
	quadratic_poly ret = quadratic_poly(prime_field::field_element(0), prime_field::field_element(0), prime_field::field_element(0));
	
	prime_field::field_element* add_mult_sum_a = new prime_field::field_element[total_uv >> 1];
	prime_field::field_element* add_mult_sum_b = new prime_field::field_element[total_uv >> 1];

	prime_field::field_element* V_mult_add_a = new prime_field::field_element[total_uv >> 1];
	prime_field::field_element* V_mult_add_b = new prime_field::field_element[total_uv >> 1];

	prime_field::field_element* addV_array_a = new prime_field::field_element[total_uv >> 1];
	prime_field::field_element* addV_array_b = new prime_field::field_element[total_uv >> 1];
	int size = total_uv >> 1;


	for(int i = 0; i < (total_uv >> 1); ++i)
	{
		int g_zero = i << 1, g_one = i << 1 | 1;
		if(current_bit == 0)
		{
			V_mult_add[i].b = V_mult_add[g_zero].b;
			V_mult_add[i].a = V_mult_add[g_one].b - V_mult_add[i].b;

			addV_array[i].b = addV_array[g_zero].b;
			addV_array[i].a = addV_array[g_one].b - addV_array[i].b;

			add_mult_sum[i].b = add_mult_sum[g_zero].b;
			add_mult_sum[i].a = add_mult_sum[g_one].b - add_mult_sum[i].b;
		}
		else
		{
			V_mult_add[i].b.value = (V_mult_add[g_zero].a.value * previous_random.value + V_mult_add[g_zero].b.value) % prime_field::mod;
			V_mult_add[i].a.value = (V_mult_add[g_one].a.value * previous_random.value + V_mult_add[g_one].b.value + prime_field::mod - V_mult_add[i].b.value) % prime_field::mod;

			addV_array[i].b.value = (addV_array[g_zero].a.value * previous_random.value + addV_array[g_zero].b.value) % prime_field::mod;
			addV_array[i].a.value = (addV_array[g_one].a.value * previous_random.value + addV_array[g_one].b.value + prime_field::mod - addV_array[i].b.value) % prime_field::mod;

			add_mult_sum[i].b.value = (add_mult_sum[g_zero].a.value * previous_random.value + add_mult_sum[g_zero].b.value) % prime_field::mod;
			add_mult_sum[i].a.value = (add_mult_sum[g_one].a.value * previous_random.value + add_mult_sum[g_one].b.value + prime_field::mod - add_mult_sum[i].b.value) % prime_field::mod;
		}


		//vectorized mpc
		add_mult_sum_a[i] = add_mult_sum[i].a; 
		add_mult_sum_b[i] = add_mult_sum[i].b; 
		V_mult_add_a[i] = V_mult_add[i].a; 
		V_mult_add_b[i] = V_mult_add[i].b; 
		addV_array_a[i] = addV_array[i].a; 
		addV_array_b[i] = addV_array[i].b;


		// ret.a.value = (ret.a.value + add_mult_sum[i].a.value * V_mult_add[i].a.value) % prime_field::mod;
		// ret.b.value = (ret.b.value + add_mult_sum[i].a.value * V_mult_add[i].b.value
		// 							+ add_mult_sum[i].b.value * V_mult_add[i].a.value
		// 							+ addV_array[i].a.value) % prime_field::mod;
		// ret.c.value = (ret.c.value + add_mult_sum[i].b.value * V_mult_add[i].b.value
		// 							+ addV_array[i].b.value) % prime_field::mod;
		
	
	}
	//vectorized mpc

	prime_field::field_element* coeff_a = multiply(size,add_mult_sum_a,V_mult_add_a);
	prime_field::field_element* coeff_b_l = multiply(size,add_mult_sum_a,V_mult_add_b);
	prime_field::field_element* coeff_b_r = multiply(size,add_mult_sum_b,V_mult_add_a);
	prime_field::field_element* coeff_c = multiply(size,add_mult_sum_b,V_mult_add_b);

	prime_field::field_element test_a(0);
	prime_field::field_element test_b(0);
	prime_field::field_element test_c(0);

	for (int i = 0; i < size; i++)
	{
		test_a = test_a + coeff_a[i];
		test_b = test_b + coeff_b_l[i] + coeff_b_r[i] + addV_array[i].a;
		test_c = test_c + coeff_c[i] + addV_array_b[i];

	}
	test_a.value = test_a.value% prime_field::mod;
	test_b.value = test_b.value% prime_field::mod;
	test_c.value = test_c.value% prime_field::mod;


	ret.a = test_a;
	ret.b = test_b;
	ret.c = test_c;

	ret.a = merge(ret.a);
	ret.b = merge(ret.b);
	ret.c = merge(ret.c);


	total_uv >>= 1;

	ret.a.value = ret.a.value % prime_field::mod;
	ret.b.value = ret.b.value % prime_field::mod;
	ret.c.value = ret.c.value % prime_field::mod;
	ret.a.value = (ret.a.value + prime_field::mod) % prime_field::mod;
	ret.b.value = (ret.b.value + prime_field::mod) % prime_field::mod;
	ret.c.value = (ret.c.value + prime_field::mod) % prime_field::mod;
	std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();

	std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t1 - t0);
	total_time += time_span.count();

	return ret;
}
std::pair<prime_field::field_element, prime_field::field_element> prover::sumcheck_finalize(prime_field::field_element previous_random)
{
	v_v = V_mult_add[0].eval(previous_random);
	return std::make_pair(v_u, v_v);
}
void prover::proof_init()
{
	//todo
}

