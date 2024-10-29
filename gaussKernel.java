package sigir.kernels;


public class gaussKernel extends kernel {
	
	public final String kernelname(){
		return "gausskernel";
	}
	
	public final double value(double distfromcenter){
		return Math.exp(-distfromcenter*distfromcenter/(2*sigma*sigma));
	}
	

	
}