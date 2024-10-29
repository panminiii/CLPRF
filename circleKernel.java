
package sigir.kernels;


public class circleKernel extends kernel {
	
	public final String kernelname(){
		return "circlekernel";
	}
	
	public final double value(double distfromcenter){
		if (distfromcenter > sigma) {
			return 0.0;
		}else{
			return Math.sqrt(1-Math.pow(distfromcenter/sigma, 2));
		}		
	}
	

	
}