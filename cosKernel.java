package sigir.kernels;


public class cosKernel extends kernel {
	
	public final String kernelname(){
		return "cosKernel";
	}
	
	public final double value(double distfromcenter){
		if (distfromcenter > sigma) {
			return 0.0;
		}else{
			return 0.5*(1.0 + Math.cos(distfromcenter*Math.PI/sigma));
		}		
	}
	

	
}