package sigir.kernels;


public class quarKernel extends kernel {
	
	public final String kernelname(){
		return "quarKernel";
	}
	
	public final double value(double distfromcenter){
		if (distfromcenter > sigma) {
			return 0.0;
		}else{
			return 15.0 * Math.pow((1-Math.pow(distfromcenter/sigma, 2)), 2)/16.0;
		}		
	}

	
}