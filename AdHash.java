package edu.sjsu.crypto.ciphersys.term;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;
import java.util.Random;

import edu.sjsu.yazdankhah.crypto.util.cipherutils.ConversionUtil;
import edu.sjsu.yazdankhah.crypto.util.cipherutils.Function;
import edu.sjsu.yazdankhah.crypto.util.primitivedatatypes.Bit;

public class AdHash implements Serializable {
	
	private static final long serialVersionUID = 1L;

	/**
	 * The rate for the miss in floating point calculation
	 * {@link AdHash#BUFFER_RATE}
	 * */
	private final static double BUFFER_RATE = 1.00001;
	
	/**
	 * Singleton Pattern usage
	 * {@link AdHash#object}
	 * */
	private static AdHash object = null;

	/**
	 * A constant value for Prime Field and modular arithmetic
	 * {@link AdHash#M}
	 * */
	private static BigInteger M;
	
	/**
	 * A constant value for the limit of the size of the inputed file under log base 2.
	 * {@link AdHash#ln_MAX_FILE_SIZE}
	 * */
	private final static int ln_MAX_FILE_SIZE = 38;
	
	/**
	 * A constant value of the total number of the inputed blocks.
	 * {@link AdHash#N}
	 * */
	private static int N;
	
	/**
	 * A constant value of the user-defined block size
	 * {@link AdHash#BLOCK_SIZE}
	 * */
	private static int BLOCK_SIZE;
	
	/**
	 * The candidates of the potential hash algorithms
	 * {@link AdHash#algorithms}
	 * */
	private static final String[] algorithms = { "MD2", "MD5", "SHA-1", "SHA-256", "SHA-384", "SHA-512" };

	/**
	 * A constant value for presenting the number of the potential candidate hash algorithms
	 * {@link AdHash#NUM_ALGORITHM}
	 * */
	private static final int NUM_ALGORITHM = 6;

	/**
	 * The random generator initialized by a user-defined seed
	 * {@link AdHash#myRandom}
	 * */
	private Random myRandom;
	
	/**
	 * The inputed file directory
	 * {@link AdHash#inputFile}
	 * */
	private String inputFile;
	
	/**
	 * The name of the selected hash algorithm
	 * {@link AdHash#myAlgorithm}
	 * */
	private String myAlgorithm;
	
	/**
	 * A table to store the generated hash code of each data block in BigInteger types
	 * {@link AdHash#hashcodes}
	 * */
	private BigInteger[] hashcodes;
	
	/**
	 * The final hash code represented in hexadecimal string
	 * {@link AdHash#finalHashcode_hex}
	 * */
	private String finalHashcode_hex;
	
	/**
	 * The length of the final hash code
	 * {@link AdHash#finalHashLength}
	 * */
	private int finalHashLength;
	
	/**
	 * A variable for storing the size of the actual usage of array.
	 * An optimization usage
	 * {@link AdHash#exact_use_block_size}
	 * */
	private int exact_use_block_size;
	
	/**
	 * A variable for storing the size of the actual usage of array(diff).
	 * An optimization usage
	 * {@link AdHash#exact_use_block_size_diff}
	 * */
	private int exact_use_block_size_diff;
	
	/**
	 * A variable for storing the number of different data blocks after comparing two inputed files
	 * {@link AdHash#exact_different_block_count}
	 * */
	private int exact_different_block_count;
	
	/**
	 * A variable for storing the execution time
	 * A performance analysis usage
	 * {@link AdHash#executionTime}
	 * */
	private double executionTime;
	
	/**
	  * A block of data read from input file.
	  * NewBlock provides a function of hashing in a multi-threads manner
	  * */
	private static class NewBlock extends Thread {
		
		/**
		 * The data inputed for hashing
		 * {@link NewBlock#data}
		 * */
		private byte[] data;
		
		/**
		 * The hash code represents the inputed data by using a selected hash algorithm
		 * {@link NewBlock#result}
		 * */
		private byte[] result;
		
		/**
		 * The offset of the inputed data block.
		 * {@link NewBlock#index}
		 * */
		private int index;
		
		/**
		 * The selected hash algorithm
		 * */
		private MessageDigest md;

		/**
		 * The destination for storing every hash code for each blocks of data
		 * {@link NewBlock#table}
		 * */
		private static BigInteger[] table = null;
		
		/**
		 * The length of the generated hash codes
		 * {@link NewBlock#hashLength}
		 * */
		private static int hashLength = -1;

		/**	
		 * The setter method
		 * {@link NewBlock#table}
		 * */
		public static void setTable(BigInteger[] _table) {
			table = _table;
		} // setTable():void

		
		/** 
		 * The getter method
		 * {@link NewBlock#table}
		 * */
		public static BigInteger[] getTable() {
			return table;
		} // getTable();

		/** 
		 * The getter method
		 * {@link NewBlock#hashLength}
		 * */
		public static int getHashLength() {
			return hashLength;
		} // getHashLength()

		/** a public constructor of Class NewBlock
		 * 
		 * @param _data: The data for hash
		 * @param _index: The offset of the inputed data
		 * @param _md: The selected hash algorithm
		 * */
		public NewBlock(byte[] _data, int _index, MessageDigest _md) {
			super("block:".concat(String.valueOf(_index)));
			this.data = _data;
			this.index = _index;
			this.md = _md;
		} // Constructor Block
		
		/** a public constructor of Class NewBlock
		 * 
		 * @param _data: The data for hash
		 * @param _index: The offset of the inputed data
		 * @param _md: The selected hash algorithm
		 * 
		 * @param _name: The name of the thread
		 * */
		public NewBlock(byte[] _data, int _index, MessageDigest _md, String _name) {
			super(_name);
			this.data = _data;
			this.index = _index;
			try {
				this.md = (MessageDigest)_md.clone();
			} catch (CloneNotSupportedException e) {
				this.md = _md;
				e.printStackTrace();
			} // end of catch MessageDigest is not cloneable;
		} // Constructor Block

		
		/** Augment the input data with the offset.
		 *  Concatenate the index in bits with the data in bits 
		 * 
		 * @return byte[] with a length of N+BLOCK_SIZE, the bytes for hash.
		 * */
		private byte[] augmentData() {
			byte[] prefix = ByteBuffer.allocate(N).putInt(this.index).array();
			byte[] temp = new byte[N + BLOCK_SIZE];
			for (int n = 0; n < N; n++)
				temp[n] = prefix[n];
			for (int d = N; d < N + BLOCK_SIZE; d++)
				temp[d] = this.data[d - N];

			return temp;
		} // augmentData():byte[]

		/** Create the hash code. The data is removed from the memory after hashing.
		 * */
		private void encode(MessageDigest _md) {
			byte[] temp = this.augmentData();
			this.result = _md.digest(temp);
			temp = null;
			this.data = null;
		} // encode():void

		/** Get the hash code in hexadecimal 
		 * 
		 * {@link NewBlock#result}
		 * @return String, the hash code in hexadecimal
		 * */
		public String getResultHex() {
			String result_in_bits = "";
			for (byte b : this.result)
				result_in_bits += String.format("%8s", Integer.toBinaryString(b & 0xFF)).replace(' ', '0');

			return result_in_bits;
		} // getResultHex():String

		/** Update the table which is shared by threads with the hash code for the assigned data block
		 * 	keyword synchronized is used for prevent race condition
		 * 
		 * @param _table: to specify which table to update
		 * */
		private synchronized void updateTable(BigInteger[] _table) {
			Bit[] result_bitArr = ConversionUtil.binStrToBitArr(this.getResultHex());
			String result_hex = ConversionUtil.bitArrToHexStr(result_bitArr);
			_table[this.index] = ConversionUtil.hexStrToBigInteger(result_hex);

			hashLength = (hashLength == -1) ? result_bitArr.length : hashLength;
		} // updateTable():void
		
		/** Update the table which is shared by threads with the hash code for the assigned data block
		 * 	keyword synchronized is used for prevent race condition
		 * 
		 * @param _content: the object to be put into the table
		 * @param _table: To specify which table to update
		 * */
		private synchronized void updateTable(Object _content, BigInteger[] _table) {
			_table[this.index] = (BigInteger) _content;
		} // updateTable():void

		/** Implement run() in the class with @Override keyword
		 * 1. Get the hash code
		 * 2. Update to the table
		 * 
		 * @throws ArrayIndexOutOfBounds from updateTable()
		 * */
		@Override
		public void run() {
			try {
				this.encode(this.md);
				this.updateTable(table);
			} catch (ArrayIndexOutOfBoundsException e) {
				System.out.println(String.valueOf(this.index).concat(" : FAIL Array Index Out of Bounds in MD."));
				this.updateTable(null, table);
			} // end of catch ArrayIndexOutOfBoundsException
		} // run():void

		/**
		 * {@link NewBlock#index}
		 * @return index, the offset of inputed block
		 * */
		public int getIndex() {
			return this.index;
		} // getIndex():int
	}
	 
	/**
	  * A block of updated data read from a new inputed file
	  * DiffBlock inheritances NewBlock 
	  * */
	private static class DiffBlock extends NewBlock {
		
		/**
		 * The second table for recording the new hash codes for the corresponding data blocks
		 * {@link DiffBlock#tableDiff}
		 * */
		private static BigInteger[] tableDiff = null;
		
		/** 
		 * The setter method
		 * {@link DiffBlock#tableDiff}
		 * */
		public static void setTable(BigInteger[] _table) {
			tableDiff = _table;
		} // setTable():void

		/** 
		 * The getter method
		 * {@link DiffBlock#tableDiff}
		 * */
		public static BigInteger[] getTable() {
			return tableDiff;
		} // getTable();

		/**
		 * A public constructor
		 * 
		 * @param _data_new: a modified/new data block
		 * @param _index: the offset of inputed data
		 * @param _md: the selected hash algorithm
		 * */
		public DiffBlock(byte[] _data_new, int _index, MessageDigest _md) {
			super(_data_new, _index, _md, "diff block:".concat(String.valueOf(_index)));
		} // constructor()

		/** Implement run() in the class with @Override keyword
		 * 1. Get the hash code
		 * 2. Update to the table
		 * 
		 * @throws ArrayIndexOutOfBounds from updateTable()
		 * */
		@Override
		public void run() {	
			while (true) {
				try {
					super.encode(super.md);
					super.updateTable(tableDiff);
					break;
				} catch (ArrayIndexOutOfBoundsException e) {
					System.out.println(String.valueOf(super.index).concat(" : FAIL Array Index Out of Bounds in MD."));
					super.updateTable(null, tableDiff);
				} // end of catch ArrayIndexOutOfBoundsException
			} // while
		} // run():void

	} // Inner class DiffBlock inheritances from NewBlock 

	/**
	 * A public method to get an instance of AdHash.(Clone)
	 * 
	 * @return returns a copy of {@link AdHash#object}
	 * */
	public static AdHash getClonedInstance() {
		return object;
	} // getClonedInstance():AdHash
	
	/**
	 * A public method to get an instance of AdHash.(Brand New or A reference)
	 * Creates a new instance of AdHash if there does not exist before.
	 * 
	 * @return returns {@link AdHash#object}
	 * */
	public static AdHash getNewInstance(String _pass, int _block_size) {
		object = new AdHash(_pass, _block_size);
		return object;
	} // getNewInstance():AdHash

	/**
	 * A public method to get an instance of AdHash.(From files)
	 * Load an instance of AdHash from a file endding with ".adhash"
	 * 
	 * @return returns {@link AdHash#object}
	 * */
	public static AdHash loadInstance(String _fileDir) {
		FileInputStream fis;
		try {
			fis = new FileInputStream(_fileDir);
			ObjectInputStream ois = new ObjectInputStream(fis);
			
			object = (AdHash) ois.readObject();
			M = (BigInteger) ois.readObject();
			N = (int) ois.readObject();
			BLOCK_SIZE = (int) ois.readObject();
			ois.close();

			return object;
		} catch (ClassNotFoundException | IOException e) {
			System.out.println("Loading fails. Returning a null object.");
			e.printStackTrace();
		}

		return null;
	} // loadInstance():AdHash

	/**
	 * Save the current instance, {@link AdHash#object} to the local directory
	 * 
	 * @param _outputDir:the output directory
	 * */
	public void save(String _outputDir) {
		try {
			FileOutputStream fos = new FileOutputStream(_outputDir);
			ObjectOutputStream oos = new ObjectOutputStream(fos);
			oos.writeObject(object);
			oos.writeObject(M);
			oos.writeObject(N);
			oos.writeObject(BLOCK_SIZE);
			oos.close();
			System.out.println("Save to [".concat(_outputDir).concat("]"));
		} catch (IOException e) {
			e.printStackTrace();
		} // end of catch IOException
	} // save:void

	/** 
	 * A private constructor
	 * 
	 * @param _pass: the seed for the random generator
	 * @param _block_size: the user-defined constant for chopping the inputed data
	 * */
	private AdHash(String _pass, int _block_size) {
		this.myRandom = Function.getRandomGenerator64(_pass);
		this.hashcodes = null;
		BLOCK_SIZE = _block_size;
		N = ln_MAX_FILE_SIZE - (int) (Math.log(BLOCK_SIZE) / Math.log(2));
	} // AdHash()
	
	/**
	 * To choose a selected hash algorithm from the pool and based on the random generator
	 * 
	 * @return A selected hash algorithm(MessageDigest object)
	 * */

	private MessageDigest algorithmOracle() throws NoSuchAlgorithmException {
		int selectedIndex = Function.generateRandomPositiveInteger(this.myRandom).mod(BigInteger.valueOf(NUM_ALGORITHM))
				.intValue();
		String algorithm = algorithms[selectedIndex];
		System.out.println(algorithm.concat(" has been selected."));
		MessageDigest hashAl = MessageDigest.getInstance(this.myAlgorithm = algorithm);
		return hashAl;
	} // algorithmOracle():MessageDigest


	/**
	 * A setter method
	 * 
	 * {@link AdHash#inputFile}
	 * */
	private void updateSourceFile(String _sourceDir) {
		this.inputFile = _sourceDir;
	} // updateSourceFile():void
	
	/**
	 * Read file and chop the data into data blocks
	 * Create NewBlock object based on the given data block
	 * Hash the data block and read from the file simultaneously
	 * 
	 * @param _inputDir: the input file directory
	 * @param _md: the selected hash algorithm
	 * 
	 * @return A array of NewBlock for managing Threads
	 * */

	private NewBlock[] getBlocksOfData(String _inputDir, MessageDigest _md) throws IOException {
		this.updateSourceFile(_inputDir);

		File file = new File(this.inputFile);
		FileInputStream fin = new FileInputStream(file);

		byte[] block = new byte[BLOCK_SIZE];
		
		long totalblock = BigInteger.valueOf(file.length()).divide(BigInteger.valueOf(BLOCK_SIZE)).longValueExact();
		
		NewBlock[] totalBlocks = new NewBlock[(int) Math.ceil(totalblock*BUFFER_RATE)];
		BigInteger[] table = new BigInteger[totalBlocks.length];
		NewBlock.setTable(table);

		int i = 0;
		for (i = 0; fin.read(block) != -1; i++) {
			totalBlocks[i] = new NewBlock(block, i, _md);
			totalBlocks[i].start();
			block = new byte[BLOCK_SIZE];
		} // for

		this.exact_use_block_size = i;
		fin.close();
		return totalBlocks;
	} // getBlocksOfData():Block[]

	
	/**
	 * Combination algorithm for generating a final hash
	 * The main idea is to add every hash code and get the summation under the modular arithmetic
	 * 
	 * @return a BigIneger
	 * */
	private BigInteger combiningOperation(BigInteger[] _table, long _start_time) {
		BigInteger result = BigInteger.valueOf(0);

		for (BigInteger b : _table)
			if ( b != null )
				result = result.add(b).mod(M);
			else
				break;
		
		if (_start_time != 0)
			System.out.println("Cost Time:".concat(String.valueOf(this.executionTime = (double)(System.currentTimeMillis()-_start_time)/1000)));
		return result;
	} // combiningOperation():BigInteger


	/**
	 * The main algorithm.
	 * 1. Choose the hash algorithm
	 * 2. Read the inputed file and create NewBlocks
	 * 3. Wait for finishing
	 * 4. Combining all hash code to get the final hash code
	 * 
	 * @param _inputDir: the file for hashing
	 * @return String, a final hash code in hexadecimal
	 * */
	public String hash(String _inputDir) {

		// choose hash algorithm
		MessageDigest algorithm = null;
		try {
			algorithm = this.algorithmOracle();
		} catch (NoSuchAlgorithmException e) {
			e.printStackTrace();
		} // end of catch no such algorithm exception

		// read file
		// chopped to blocks
		// encrypt
		NewBlock[] data = null;
		long start_t = System.currentTimeMillis();
		
		
		try {
			data = this.getBlocksOfData(_inputDir, algorithm);
		} catch (IOException e) {
			e.printStackTrace();
		} // end of catch IOException

		// wait for finish
		try {
			int b;
			for ( b = 0; b < data.length; b ++) {
				if ( data[b] != null) {
					// data[b].start();
					data[b].join();
				} // if
				else
					break;
			} // for
			
		} catch (InterruptedException e) {
			e.printStackTrace();
		} // end of catch InterruptedException

		this.hashcodes = NewBlock.getTable();

		// add together
		int hashLength = NewBlock.getHashLength();
		M = Function.generateRandomPrimeBigInteger(hashLength + 4, this.myRandom);
		BigInteger finalHash = this.combiningOperation(this.hashcodes, start_t);

		// Output to file
		this.finalHashLength = hashLength;
		
		return (this.finalHashcode_hex = ConversionUtil.bigIntegerToHexStr(finalHash, hashLength));
	} // hash():String



	/**
	 * Read file and chop the data into data blocks when a new file is used for updating the old hash code
	 * Create DiffBlock object based on the given data block and only create when the data is inconsistent with the previous data block
	 * Hash the data block and read from the file simultaneously
	 * 
	 * Read two file at the same time, the old one and the new new.
	 * 
	 * @param _inputDir: the input file directory, a new file
	 * @param _md: the selected hash algorithm
	 * 
	 * @return A array of NewBlock for managing Threads
	 * */
	private DiffBlock[] markDifference(String _inputDir, MessageDigest _md) throws IOException {

		File file_org = new File(this.inputFile);
		FileInputStream fin_org = new FileInputStream(file_org);
		
		File file = new File(_inputDir);
		FileInputStream fin = new FileInputStream(file);

		byte[] block = new byte[BLOCK_SIZE];
		byte[] block_diff = new byte[BLOCK_SIZE];
		
		long num_totalblock = BigInteger.valueOf(file.length()).divide(BigInteger.valueOf(BLOCK_SIZE)).longValueExact();
		DiffBlock[] totalBlocks_diff = new DiffBlock[(int) Math.ceil(num_totalblock*BUFFER_RATE)];
		BigInteger[] table_diff = new BigInteger[totalBlocks_diff.length];
		DiffBlock.setTable(table_diff);
		
		int end_diff = 0, end = 0;
		int index_totalBlocks_diff = 0;
		if (file_org.length() < file.length() ) {
			while ( fin_org.read(block) != -1) {
				
				fin.read(block_diff);
				if ( !Arrays.equals(block, block_diff)) {
					totalBlocks_diff[index_totalBlocks_diff] = new DiffBlock(block_diff, end_diff, _md);
					totalBlocks_diff[index_totalBlocks_diff++].start();
					
					block = new byte[BLOCK_SIZE];
					block_diff = new byte[BLOCK_SIZE];
				} // if 
				else {
					table_diff[end_diff] = this.hashcodes[end];
				} // else
				
				end += 1;
				end_diff += 1;
			} // while
			
			if ( end != this.exact_use_block_size ) {
				fin.close();
				fin_org.close();
				throw new IOException();
			} // if
			
			while ( fin.read(block_diff) != -1) {
				totalBlocks_diff[index_totalBlocks_diff] = new DiffBlock(block_diff, end_diff, _md);
				totalBlocks_diff[index_totalBlocks_diff++].start();
				
				block_diff = new byte[BLOCK_SIZE];
				end_diff += 1;
			} // while 
			
			this.exact_use_block_size_diff = end_diff;
		} // if 
		else {
			while ( fin.read(block_diff) != -1 ) {
				fin_org.read(block);
				
				if (!Arrays.equals(block, block_diff)) {
					totalBlocks_diff[index_totalBlocks_diff] = new DiffBlock(block_diff, end_diff, _md);
					totalBlocks_diff[index_totalBlocks_diff++].start();
					
					block = new byte[BLOCK_SIZE];
					block_diff = new byte[BLOCK_SIZE];
				} // if
				else {
					table_diff[end_diff] = this.hashcodes[end];
				} // else

				end += 1;
				end_diff += 1;	
			} // while 

			this.exact_use_block_size_diff = end_diff;
		} // else

		this.exact_different_block_count = index_totalBlocks_diff;
		fin_org.close();
		fin.close();
		
		return totalBlocks_diff;
	} // getBlocksOfData():Block[]


	/**
	 * Update the old hash code with the new hash values.
	 * Inversion actions are required.
	 * The inverse actions are provided base on the concepts and the property of Prime Field under the modular arithmetic
	 * 
	 * @param _org: an old table which contains every hash code corresponding to the old data blocks
	 * @param _diff: a table which contains every hash code corresponding to the new data blocks while only the changed blocks have the hash code.
	 * @param _final: the old final hash value
	 * @param _start_time: for performance analysis usage
	 * 
	 * @return a new final hash code in BigInteger
	 * */
	private BigInteger updateHashcode( BigInteger[] _org, BigInteger[] _diff, DiffBlock[] _diffBlock, BigInteger _final, long _start_time ) {
		
		int length_org = this.exact_use_block_size;
		int length_diff = this.exact_use_block_size_diff;
		
		int index = 0;
		
		int changeB = 0;
		int newB = 0;
		int removeB = 0;
		
		// change blocks
		for ( int db = 0; db < this.exact_different_block_count; db ++ ) {
			index = _diffBlock[db].getIndex();
			
			if ( index < length_org) {
				// replace
				changeB += 1;
				BigInteger inverse_hash = M.subtract(_org[index]);
				BigInteger newhash = _diff[index];
				_final = _final.add(inverse_hash).add(newhash).mod(M);			
			} // if 
			else {
				// add new
				newB += 1;
				BigInteger newhash = _diff[index];
				_final = _final.add(newhash).mod(M);
			} // else
		} // for 
		
		if ( length_diff < length_org) {			
			for ( index = length_diff; index < length_org; index ++) {
				// remove blocks
				removeB += 1;
				BigInteger inverse_hash = M.subtract(_org[index]);
				_final = _final.add(inverse_hash).mod(M);
			} // for
		} // if 


		System.out.println("Cost Time:".concat(String.valueOf(this.executionTime = (double)(System.currentTimeMillis()-_start_time)/1000)));
		System.out.println("New Blocks Added: ".concat(String.valueOf(newB)));
		System.out.println("Remove Blocks Added: ".concat(String.valueOf(removeB)));
		System.out.println("Change Blocks Added: ".concat(String.valueOf(changeB)));
		System.out.println("Change rate: ".concat(String.valueOf((double)changeB/this.exact_use_block_size)));
		return _final;
	} // updateHashcode():BigInteger


	/** 
	 * The main function to update a hash code based on a previous record.
	 * 
	 * An old record is required; otherwise, the method cannot work correctly.
	 * 
	 * 1. Loaded data check
	 * 2. If the check passes, then continues
	 * 3. Load the new files and find the different blocks
	 * 4. wait for result
	 * 5. update the old hash value 
	 * 
	 * @param _inputDir: the directory of the new file
	 * 
	 * @return a final hash value in hexadecimal
	 * */
	public String update(String _inputDir) {
		if (hashcodes == null) {
			return "Update fails, previous record does not exist.";
		} // if

		System.out.println("Old file: ".concat(this.inputFile));
		System.out.println("New file: ".concat(_inputDir));
		
		NewBlock.setTable(this.hashcodes);
		BigInteger finalHash = this.combiningOperation(this.hashcodes, 0);
		
		
		if (this.finalHashcode_hex.compareTo(finalHashcode_hex) == 0) {
			System.out.println("Hashcode loaded: " .concat(finalHashcode_hex));
		
			DiffBlock[] newFileBlock = null;
			MessageDigest md = null;
			try {
				md = MessageDigest.getInstance(this.myAlgorithm);
			} catch (NoSuchAlgorithmException e1) {
				e1.printStackTrace();
			} // end of catch NoSuchAlgorithmException 

			long start_t = System.currentTimeMillis();
			try {
				newFileBlock = this.markDifference(_inputDir, md);
			} catch (IOException e) {
				e.printStackTrace();
			} // end of catch IOEXception
			
			try {
				for ( int db = 0; db < this.exact_different_block_count; db ++ ) {
					// newFileBlock[db].start();
					newFileBlock[db].join();
				} // for
			} catch (InterruptedException e) {
				e.printStackTrace();
			} // end of catch InterruptedException
			
			BigInteger[] hashcodes_diff = DiffBlock.getTable();
			finalHash = this.updateHashcode(this.hashcodes, hashcodes_diff, newFileBlock, finalHash, start_t);

			this.updateSourceFile(_inputDir);
			this.hashcodes = hashcodes_diff;
			this.exact_use_block_size = this.exact_use_block_size_diff;
			
			
			BigInteger finalHash_fromTable = this.combiningOperation(this.hashcodes, 0);
			if (finalHash.subtract(finalHash_fromTable).intValueExact() == 0)
				return this.finalHashcode_hex = ConversionUtil.bigIntegerToHexStr(finalHash, finalHashLength);
			else
				return "Update fails, hashcode consistency check fail.";
		} // if 
		else {
			return "Update fails, hashcode recovered fail.";
		} // else
	} // update():String
	
	/** 
	 * A tradition approach of hashing a file by using MessageDigest
	 * 
	 * A performance analysis usage
	 * 
	 * @return a final hash code in hexadecimal
	 * */
	
	public String hash_tradition( String _fileDir) {
		
		// choose hash algorithm
		MessageDigest algorithm = null;
		try {
			algorithm = this.algorithmOracle();
		} catch (NoSuchAlgorithmException e) {
			e.printStackTrace();
			return "Algorithm not found Error";
		} // end of catch no such algorithm exception
		
		try {
			long start_t = System.currentTimeMillis();
			File file = new File(_fileDir);
			FileInputStream fin = new FileInputStream(file);
			byte[] block = new byte[BLOCK_SIZE];
			while ( fin.read(block) != -1 ) 
				algorithm.update(block);
			fin.close();
			
			byte[] result = algorithm.digest();
			
			String result_in_bits = "";
			for (byte b : result)
				result_in_bits += String.format("%8s", Integer.toBinaryString(b & 0xFF)).replace(' ', '0');
			
			Bit[] result_bitArr = ConversionUtil.binStrToBitArr(result_in_bits);
			String result_hex = ConversionUtil.bitArrToHexStr(result_bitArr);
			System.out.println("Cost Time:".concat(String.valueOf(this.executionTime = (double)(System.currentTimeMillis()-start_t)/1000)));
			
			return result_hex;
		} catch (IOException e) {
			e.printStackTrace();
			return "IO Error";
		} // end of catch FileNotFoundException
		
	} // hash_tradition():String
	

	/**
	 * A getter method
	 * 
	 * {@link AdHash#executionTime}
	 * */
	public double getExeTime() {
		return this.executionTime;
	} // getExeTime():double
} // class AdHash

