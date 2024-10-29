package sigir.kernels;


public class triweightKernel extends kernel {
	
	public final String kernelname(){
		return "triweightKernel";
	}
	
	public final double value(double distfromcenter){
		if (distfromcenter > sigma) {
			return 0.0;
		}else{
			return 35.0 * Math.pow((1-Math.pow(distfromcenter/sigma, 2.0)), 3.0)/32.0;
		}		
	}
	

	
}