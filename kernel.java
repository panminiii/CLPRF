package sigir.kernels;

public abstract class kernel {
	
	public double sigma = 12.5;
	
	public void setParameter(double s){
		this.sigma = s;
	}
	
	public abstract String kernelname();
	
	public abstract double value(double distfromcenter);
	
	public double intersect(double distbetween){
		return value(distbetween/2.0);
	}
	
}