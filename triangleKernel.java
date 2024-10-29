package sigir.kernels;


public class triangleKernel extends kernel {
	
	public final String kernelname(){
		return "triangleKernel";
	}
	
	public final double value(double distfromcenter){
		if (distfromcenter > sigma) {
			return 0.0;
		}else{
			return 1.0 - distfromcenter/sigma;
		}		
	}
	

	
}