package sigir.kernels;

public class reverseKernel extends kernel {
	
	public final String kernelname(){
		return "reversekernel";
	}
	
	public final double value(double distfromcenter){
		return 1/(sigma*distfromcenter+1);
	}
	
	
}