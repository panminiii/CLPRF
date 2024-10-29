package sigir.kernels;


public class epanKernel extends kernel {
	
	public final String kernelname(){
		return "epanKernel";
	}
	
	public final double value(double distfromcenter){
		if (distfromcenter > sigma) {
			return 0.0;
		}else{
			return 3.0 * (1-Math.pow(distfromcenter/sigma, 2))/4.0;
		}		
	}	

	
}