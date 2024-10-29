package sigir;

import java.io.BufferedReader;

import org.apache.commons.io.FileUtils; 
import org.json.JSONObject; 
import java.io.File; 
import java.io.IOException; 
import org.json.JSONArray;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import org.apache.lucene.benchmark.quality.Judge;
import org.apache.lucene.benchmark.quality.QualityQuery;
import org.apache.lucene.benchmark.quality.QualityQueryParser;
//import org.apache.lucene.benchmark.quality.QualityStats;
import org.apache.lucene.benchmark.quality.trec.TrecJudge;
import org.apache.lucene.benchmark.quality.trec.TrecTopicsReader;
import org.apache.lucene.benchmark.quality.utils.DocNameExtractor;
import org.apache.lucene.index.AtomicReader;
import org.apache.lucene.index.DirectoryReader;
import org.apache.lucene.index.DocsAndPositionsEnum;
import org.apache.lucene.index.DocsEnum;
import org.apache.lucene.index.Fields;
import org.apache.lucene.index.IndexReader;
import org.apache.lucene.index.MultiFields;
import org.apache.lucene.index.SlowCompositeReaderWrapper;
import org.apache.lucene.index.Term;
import org.apache.lucene.index.Terms;
import org.apache.lucene.index.TermsEnum;
import org.apache.lucene.search.DocIdSetIterator;
import org.apache.lucene.search.IndexSearcher;
import org.apache.lucene.search.Query;
import org.apache.lucene.search.ScoreDoc;
import org.apache.lucene.search.TopDocs;
import org.apache.lucene.store.Directory;
import org.apache.lucene.store.FSDirectory;
import org.apache.lucene.util.BytesRef;

import sigir.kernels.kernel;

public class Retrieval_BKRoc {
	
	private static final String docNameField = "docno";
	private static final String docContentField = "contents";
	QualityQuery[] qualityQueries;
	QualityQueryParser qqParser;	// Parse a QualityQuery into a Lucene query.
	IndexReader reader;
	IndexSearcher searcher;
	Judge judge;
	kernel myKernel;
	//	PrintWriter qualityLogBM25;SubmissionReport submitRepBM25;SubmissionReport submitRepCRTER2;
	PrintWriter qualityLogCRoc;
	
	public static String[] topics={"topics/topics.AP90.51-100","topics/topics.AP8889.51-100","topics/topics.disk12.51-200","topics/topics.disk45.301-450","topics/topics.wt2g","topics/topics.wt10g","topics/topics.FT.301-400","topics/topics.FBIS.351-450","topics/topics.LA.301-400","topics/topics.SJMN.51-150","topics/topics.WSJ.151-200","topics/topics.GOV2.801-850"}; 
	public static String[] qrels={"qrels/qrels.AP90.51-100","qrels/qrels.AP8889.51-100","qrels/qrels.disk12.51-200","qrels/qrels.disk45.301-450","qrels/qrels.wt2g","qrels/qrels.wt10g","qrels/qrels.FT.301-400","qrels/qrels.FBIS.351-450","qrels/qrels.LA.301-400","qrels/qrels.SJMN.51-150","qrels/qrels.WSJ.151-200","qrels/qrels.GOV2.801-850"}; 
	public static String[] index={"G:/users/hx/ir/index/index418_AP90","G:/users/hx/ir/index/index418_AP8889","G:/users/hx/ir/index/index_disk12","G:/users/hx/ir/index/index_DISK45-NO-CR","G:/users/hx/ir/index/index_wt2g","G:/users/hx/ir/index/index_wt10g"};
	public static String[] dataName={"AP90_KBert","AP8889_KBert","disk12_KBert","disk45_KBert","wt2g_KBert","wt10g_KBert","FT_KBert","FBIS_KBert","LA_KBert","SJMN_KBert","WSJ_KBert","GOV2_KBert"};
	public static String[] jsonName={"AP90_KBert.json","AP8889_KBert.json","disk12_KBert.json","first_round_BM25_BERT_Sco/disk45_BM25_query_article(4500).json","wt2g_KBert.json","first_round_BM25_BERT_Sco/wt10g_BM25_query_article(4500).json"};
	public static String json_Name;
	
	
	int numDocs;
	int maxResults = 1000;
	double avg_doc_length;
	static int N=10;
	static int N1=30;
	static double alpha=1.0;
	static double beta=0.1;
	static double k1 = 1.2;
	static double b = 0.25;
	static double k3 = 8.0;
	static double sigma=50;
	
	public Retrieval_BKRoc() {
	}

	public static void main(String[] args) throws Throwable {
		String kernelName="gaussKernel";       // 确定交叉计算函数
		kernel newKernel=(kernel)Class.forName("sigir.kernels."+kernelName).newInstance();
		for (int i=3;i<=3;i+=1) {
			json_Name=jsonName[i];
			for (N1=10;N1<=20;N1+=10) {
				if (N1==40)	continue;
				for (int j=8;j>=0;j-=1) {
					switch(i)
					{                     // 确定每个数据集最好的b值
						case 0:b=0.55;alpha=0.43;beta=0.2;break;
						case 1:b=0.0 ;alpha=0.29;beta=0.5;break;
						case 2:b=0.35;alpha=0.5;beta=0.3;break;
						case 3:b=0.35;alpha=0.54;beta=0.33;break;
						case 4:b=0.25;alpha=0.2;beta=0.6;break;
						case 5:b=0.2;alpha=0.4;beta=0.8;break;
						case 6:b=0.3;break;
						case 7:b=0.05;break;
						case 8:b=0.3;break;
						case 9:b=0.55;alpha=0.6;beta=0.2;break;
						case 10:b=0.3;alpha=0.5;beta=0.5;break;
						case 11:b=0.4;alpha=0.2;beta=0.2;break;
					}    
					switch(j)
					{                     // 确定每个数据集最好的b值
						case 0:sigma=10;break;
						case 1:sigma=25;break;
						case 2:sigma=50;break;
						case 3:sigma=80;break;
						case 4:sigma=100;break;
						case 5:sigma=200;break;
						case 6:sigma=500;break;
						case 7:sigma=1000;break;
						case 8:sigma=1500;break;
						
					}    
					
					for(alpha=0.2;alpha<=0.6;alpha=round(alpha+0.2)){
						for(beta=0.2;beta<=0.6;beta=round(beta+0.2)){
							String resultFile="result/result152/Bkroc/N=4500/disk45/N=1020/"+dataName[i]+"-b="+b+"-"+kernelName+"-sigma="+sigma+"-alpha="+alpha+"-beta="+beta+"-N="+N+"-N1="+N1+"_p1.txt";
							String reportFile="report/kroc13/"+dataName[i]+"-b="+b+"-"+kernelName+"-sigma="+sigma+"-alpha="+alpha+"-beta="+beta+"-N="+N+"-N1="+N1+"8.txt";
							System.out.println(resultFile);  //pan test
							new Retrieval_BKRoc().RunCRTER2(topics[i],qrels[i],index[i],newKernel, sigma,resultFile, reportFile);
						}
					}	
				}
			}
		}
	}

	public void RunCRTER2(String topicFile, String qrelsFile, String indexFile,kernel myKernel, double sigma,String resultFile, String reportFile) throws Exception {
		this.myKernel=myKernel;
		myKernel.setParameter(sigma);
		Directory directory = FSDirectory.open(new File(indexFile));
		reader = DirectoryReader.open(directory);
		searcher = new IndexSearcher(reader);
		qualityLogCRoc = new PrintWriter(new File(resultFile), "UTF-8");
		TrecTopicsReader qReader = new TrecTopicsReader();	// #1
		qualityQueries = qReader.readQueries(new BufferedReader(new FileReader(new File(topicFile))));	// #1 Read TREC topics as QualityQuery[]
		judge = new TrecJudge(new BufferedReader(new FileReader(new File(qrelsFile))));	// #2 Create Judge from TREC Qrel file
		judge.validateData(qualityQueries, qualityLogCRoc); // #3 Verify query and Judge match
		qqParser = new MyQQParser("title", "contents"); // #4 Create parser to translate queries into Lucene queries
		//submitRepCRTER2 = new SubmissionReport(new PrintWriter(new File(reportFile), "UTF-8"), "TEST");
		execute();    //核心函数
		directory.close();
		qualityLogCRoc.close();
	}

	HashMap<String, Long> term_total_freq_map = new HashMap<String, Long>();		// term frequency in collection(CTF)
	HashMap<String, Integer> term_doc_freq_map = new HashMap<String, Integer>();	// term frequency in a document(DF)
	HashMap<Integer, Integer> doc_length_map = new HashMap<Integer, Integer>();		// document length
	HashMap<Integer, Double> doc_avg_tf_map = new HashMap<Integer, Double>();		// average of term frequency in a document
	HashMap<String, HashMap<Integer, ArrayList<Integer>>> within_query_freq_map = new HashMap<String, HashMap<Integer, ArrayList<Integer>>>(); // 存放每个词在每篇文档的位置信息
	
	public void execute() throws Exception {
		termStats();
		docStats();
		search();
	}
	
	/** termStats() 从term的角度处理，每个词条的总词频ctf，每个词条出现在多少文档中df，所有文档的总长度total_tf **/
	public void termStats() throws Exception {
		Fields fields = MultiFields.getFields(reader);       // 读取索引
		Terms terms = fields.terms(docContentField);         // 得到倒排索引 词条（term）表
		TermsEnum iterator = terms.iterator(null);           // 构建迭代器
		BytesRef byteRef = null;
		while ((byteRef = iterator.next()) != null) {        // 遍历整个倒排索引表，获得每个词条的总词频ctf，每个词条出现在多少文档中df，所有文档的总长度total_tf
			String term = new String(byteRef.bytes, byteRef.offset, byteRef.length);
			term_total_freq_map.put(term, iterator.totalTermFreq());
			term_doc_freq_map.put(term, iterator.docFreq());
		}
		System.err.print("go1--");
		//System.out.println("num of terms: " + term_total_freq_map.size());
		//System.out.println("total_term_freq: " + total_term_freq);
	}

	/** docStats() 从文档的角度处理，获得每篇文档的长度，每篇文档的平均词频，所有文档的平均长度 **/
	public void docStats() throws Exception {               
		long total_dl = 0;
		for (int j = 0; j < reader.numDocs(); j++) {
			int docLen = 0;
			int term_num = 0;
			Terms terms = reader.getTermVector(j, docContentField);
			if (terms != null && terms.size() > 0) {
				TermsEnum termsEnum = terms.iterator(null);
				while ((termsEnum.next()) != null) {
					int freq = (int) termsEnum.totalTermFreq();
					docLen += freq;
					term_num++;
				}
			}
			total_dl += docLen;
			doc_length_map.put(j, docLen);
			double avg_tf = (term_num == 0) ? 0 : ((double) docLen) / term_num;
			doc_avg_tf_map.put(j, avg_tf);
		}
		avg_doc_length = ((double) total_dl) / reader.numDocs();
		System.err.print("go2---");
	}

	/**CrosstermStats(term_list,BM25_doc_set) 根据词条表，文档编号集合计算这些词条在文档集合中的位置并保存下来 **/
	public void CrosstermStats(ArrayList<Term> term_list,Set<Integer> BM25_doc_set) throws Exception {
		AtomicReader atomicReader = SlowCompositeReaderWrapper.wrap(reader);
			for (int k = 0; k < term_list.size(); k++) {
				Term term = term_list.get(k);                                 //termtext  词条文本
				String termText = term.text();
				DocsAndPositionsEnum docsAndPositionsEnum = atomicReader.termPositionsEnum(term);   //某个具体词条的倒排表，这个表是文章号和位置信息
				if (docsAndPositionsEnum == null) {
					continue;
				}             // 如果该次的倒排表为空，则下一个
				int doc_id;
				HashMap<Integer, ArrayList<Integer>> Docid_position_map = new HashMap<Integer, ArrayList<Integer>>();     //这个map用来存放文档号和 每个文档号中该词条的所有位置信息
				while ((doc_id = docsAndPositionsEnum.nextDoc()) != DocIdSetIterator.NO_MORE_DOCS) {
					if(!BM25_doc_set.contains(doc_id)) continue;  // pan add 只处理set中有文档编号的，set中没有编号的不处理
					int freq = docsAndPositionsEnum.freq();       //该文档中出现词条的个数
					int position;
					ArrayList<Integer> query_terms_position = new ArrayList<Integer>();  //位置列表
					for (int j = 0; j < freq; j++) {
						position = docsAndPositionsEnum.nextPosition();
						query_terms_position.add(position);                          //获取每一个位置填充到列表中
					}
					Docid_position_map.put(doc_id, query_terms_position);       //将文档号和位置列表放入位置map中
				}
				within_query_freq_map.put(termText, Docid_position_map);     //将某一词条和该词条的文档号的位置列表map存在一个新的map中
			}
	}

	public void search() throws Exception {
		AtomicReader atomicReader = SlowCompositeReaderWrapper.wrap(reader);
		QualityStats statsCRoc[] = new QualityStats[qualityQueries.length];
		//雪彦add
		File file=new File(json_Name);              ////////////////////////////////
		String content= FileUtils.readFileToString(file,"UTF-8"); 
		JSONArray jsonArray=new JSONArray(content);
		
		
		for (int i = 0; i < qualityQueries.length; i++) {
			System.err.println(i+" ");
			QualityQuery qq = qualityQueries[i];
			Query query = qqParser.parse(qq);
			HashSet<Term> term_set = new HashSet<Term>();
			query.extractTerms(term_set);
			ArrayList<Term> term_list = new ArrayList<Term>();
			for (Term term : term_set) {
				DocsEnum docsEnum = atomicReader.termDocsEnum(term);	            // 某个词条的按文档的倒排索引 例如  word-》1-》3-》4... word代表查询的词条，1,3,4代表出现该词的文档
				if(docsEnum!=null)
				term_list.add(term);
			}
			
			Set<Integer> doc_set = new HashSet<Integer>();
			int[][] freq_array = new int[term_list.size()][reader.numDocs()];
			for (int k = 0; k < term_list.size(); k++) {
				Term term = term_list.get(k);
				DocsEnum docsEnum = atomicReader.termDocsEnum(term);
				if (docsEnum == null) {
					continue;
				}
				while (docsEnum.nextDoc() != DocIdSetIterator.NO_MORE_DOCS) {
					int doc_id = docsEnum.docID();
					doc_set.add(doc_id);
					freq_array[k][doc_id] = docsEnum.freq();
				}
			}
			numDocs = reader.numDocs();
			
			//第一次检索用BM25方式//**pan add**//
//			ScoreDoc[] compact_score_array_BM25=QueryExe(doc_set,term_list,freq_array);   //先进行BM25得到得分排序
//			
//			int doc_min=Math.min(N, compact_score_array_BM25.length);        //求要处理的文档个数，返回结果大于20的取20.小于20的取具体个数
//			Set<Integer> BM25_doc_set = new HashSet<Integer>();              //将前min个的文档编号存放到set中
//			for(int doc_i=0;doc_i < doc_min ;doc_i++)
//			{
//				BM25_doc_set.add(compact_score_array_BM25[doc_i].doc);
//			}
			//雪彦add	
			ScoreDoc[] compact_score_array_BM25BERT=QueryExe(doc_set,term_list,freq_array,jsonArray,i);   //先进行BM25得到得分排序
			int doc_min=Math.min(N, compact_score_array_BM25BERT.length);        //求要处理的文档个数，返回结果大于20的取20.小于20的取具体个数
			Set<Integer> BM25_doc_set = new HashSet<Integer>();              //将前min个的文档编号存放到set中
			for(int doc_i=0;doc_i < doc_min ;doc_i++)
			{
				BM25_doc_set.add(compact_score_array_BM25BERT[doc_i].doc);
			}
			
			//term_list1获得前N篇文档的所有词条
			ArrayList<Term> term_list1=new ArrayList<Term>();                              //构建前N篇文档的所有的词条集合
			for(int n=0;n<doc_min;n++)
			{
				int docNum=compact_score_array_BM25BERT[n].doc;                              // 获得第一次查询后的前n篇文档的文档号码
				Terms terms = reader.getTermVector(docNum, docContentField);	         // 根据文档号码提取该文档的词条倒排表			
				TermsEnum iterator = terms.iterator(null);                                  
				BytesRef byteRef = null;
				while ((byteRef = iterator.next()) != null) {  
				    String term_text = new String(byteRef.bytes, byteRef.offset, byteRef.length);
				    Term term = new Term(docContentField,term_text );
				    if(!term_list1.contains(term))
				    	term_list1.add(term);                                               // 将所有的词条封装成Term格式保存
				}
			}
			
			/**********************  EQ(BM25:TF*IDF) **************************************/
			//**潘 伪相关反馈***  计算前n篇文档中每个词构成的向量每个词条的tf*idf
			ArrayList<HashMap<String,Double>> DocN_list1 = new ArrayList<HashMap<String,Double>>(); 
			for(int n=0;n<doc_min;n++)
			{
				HashMap<String,Double> Vecter_DocN1 = new HashMap<String,Double>();
				int j=compact_score_array_BM25BERT[n].doc;                              // 获得第一次查询后的前n篇文档的文档号码
				double dl= doc_length_map.get(j); 
				//double K = k1 * ((1 - b) + b * dl / avg_doc_length);
				Terms terms = reader.getTermVector(j, docContentField);	    // 根据文档号码提取该文档的词条倒排表			
				TermsEnum iterator = terms.iterator(null);                                  
				BytesRef byteRef = null;
				while ((byteRef = iterator.next()) != null) {  
				    String term = new String(byteRef.bytes, byteRef.offset, byteRef.length);
					double tf=iterator.totalTermFreq();                               // tf
					tf=tf/dl;
					double df=term_doc_freq_map.get(term);                            // 根据词条文本得到在多少篇文档中出现
					//double TF = (k1 + 1) * tf / (K + tf);
					double IDF = log2((numDocs - df + 0.5) / (df + 0.5)); 
					Vecter_DocN1.put(term, tf*IDF/N);                             // 计算出每个词条的tf*idf并保存到文档向量中
					//Vecter_DocN1.put(term, TF*IDF/N);                             // 计算出每个词条的tf*idf并保存到文档向量中
					
				}
				DocN_list1.add(Vecter_DocN1);                                           // 将所有的文档向量保存到文档列表中
			}
			HashMap<String,Double> sum_DocN1=new HashMap<String,Double>();
			for(int m=0;m<DocN_list1.size();m++)
			{
				sum_DocN1=addVecter(sum_DocN1, DocN_list1.get(m),1.0,1.0);                       // 所有的文档向量求和 sum(ri)
			}			
						
			//**潘 伪相关反馈***  构建新的查询q1=a*q0+b*sum(ri)/abs(Df)  ri==terms_i(tf_i*idf_i+)
			/********************** alpha*q0+beta*((1-deta)*(TF*IDF)+deta*(CrossTF*IDF)) **************************************/
			//求出所有词条在每个文档中的位置信息
			CrosstermStats(term_list1,BM25_doc_set);                                    // 将set传到要处理的函数中
			//构建前N篇文档的N个向量
			ArrayList<HashMap<String,Double>> DocN_list = new ArrayList<HashMap<String,Double>>();  //每一篇文档向量构成的得分
			//计算每个文档中的每个词条与查询词条之间的Crossterm得分
			for (int n = 0; n < doc_min; n++) {                                          //开始计算所返回的前n篇文档的，每个文档向量得分     
				HashMap<String,Double> Vecter_DocN = new HashMap<String,Double>();
				int j=compact_score_array_BM25BERT[n].doc;  
				int dl = doc_length_map.get(j);                                 //第j篇文档的长度
				double K = k1 * ((1 - b) + b * dl / avg_doc_length);
				ArrayList<Term> term_list_tmp=new ArrayList<Term>();
				Terms terms = reader.getTermVector(j, docContentField);	    // 根据文档号码提取该文档的词条倒排表			
				TermsEnum iterator = terms.iterator(null);                                  
				BytesRef byteRef = null;
				while ((byteRef = iterator.next()) != null) {  
					String term_text = new String(byteRef.bytes, byteRef.offset, byteRef.length);
				    Term term = new Term(docContentField,term_text );
				    if(!term_list_tmp.contains(term))
				    	term_list_tmp.add(term);                                        // 将一篇文档的词条封装成Term格式保存
				}
				
				for (int ti = 0; ti < term_list_tmp.size(); ti++) {                     // ti为这一篇文档的每一个词条
					double ptf = 0.0;
					int tftiD = within_query_freq_map.get(term_list_tmp.get(ti).text()).get(j).size();   //ti在第j篇文档中出现的次数
					
					for (int qj = 0; qj < term_list.size(); qj++) {                     // qj为查询中的每一个词条
						double tftiqjD = 0;                                                 // 统计新的TF
						int tfqjD = freq_array[qj][j];                        // qj在j文档中的次数
						double qtf = myKernel.intersect(1);                   // 距离计算函数的选择
						
						if (tftiD == 0 || tfqjD == 0) {
							continue;
						}
						
						for (int tk = 0; tk < tftiD; tk++) {                  // 依次计算ti的每一个位置tk，对应qj的每一个位置的计算，双重循环处理
							int positionkti = within_query_freq_map.get(term_list_tmp.get(ti).text()).get(j).get(tk);
							for (int qk = 0; qk < tfqjD; qk++) {
								int positionkqj = within_query_freq_map.get(term_list.get(qj).text()).get(j).get(qk);
								double kerneltermp = myKernel.intersect(Math.abs(positionkti - positionkqj)); // 对两个位置的求差的绝对值，然后带入相关的距离函数中求值
								if (kerneltermp >= Double.MIN_VALUE) {              // 如果值有效，则累加，并求出有效次数
									tftiqjD += kerneltermp;
								} 
							}     
						} 
						//if(tftiD!=0) tftiqjD=tftiqjD/tftiD;
						//double TFtiqjD = (k1 + 1) * tftiqjD / (K + tftiqjD);
						double TFtiqjD = tftiqjD/ (K + tftiqjD);
						//System.err.println("  "+TFtiqjD+"  ");
						int qjdf=term_doc_freq_map.get(term_list.get(qj).text());   //出现查询词qj的文档篇数
					    double IDFqj = log2((numDocs - qjdf+ 0.5) / (qjdf + 0.5));
						double QTF = (k3 + 1) * qtf / (k3 + qtf);
						ptf += TFtiqjD * IDFqj * QTF;                         //  某一个文档中的一个词条与一条查询的Cross得分
						
					}
					if(ptf/N!=0){
						Vecter_DocN.put(term_list_tmp.get(ti).text(), ptf/N);    // 每一个文档的corssterm得分向量
					}
				}
				DocN_list.add(Vecter_DocN);                                              // N个文档的corssterm得分向量
			}
			HashMap<String,Double> sum_DocN=new HashMap<String,Double>();
			for(int m=0;m<DocN_list.size();m++)
			{
				sum_DocN=addVecter(sum_DocN, DocN_list.get(m),1.0,1.0);              // 对求得的N个文档向量求和即 sum(ri)/N
			}			
			
			
			HashMap<String,Double> q_Doc=new HashMap<String,Double>();
			for(Term t:term_list)              
			{
				q_Doc.put(t.text(), 1.0);                                             // 将查询的词条以权重1放入新的文档向量q_Doc中
			}
			
			HashMap<String,Double> pre_DocN1=new HashMap<String,Double>();
			HashMap<String,Double> pre_DocN=new HashMap<String,Double>();
			pre_DocN1=sortVecter1(sum_DocN1);                                // 将文档向量排序呢并且返回最大的N1个词条  Q1
			pre_DocN=sortVecter1(sum_DocN);                                           // 将文档向量排序呢并且返回最大的N1个词条  Q2
			
			pre_DocN1=addVecter(pre_DocN1,pre_DocN,1-beta,beta);                    // BM25+kernel按公式求新的q1 q1=alpha*q0+beta*((1-deta)*TFIDF+
//			pre_DocN1=sortVecter(pre_DocN1);                                          // 还原为标准的反馈词个数
			
			pre_DocN=addVecter(q_Doc,pre_DocN1,1-alpha,alpha);//原始和扩展
			
			/** 根据q1和权重进行第二次查询，得到根据文档得分排好顺序的文档数组，调用函数PFB_QueryExe **/
			ScoreDoc[] compact_score_arrayKRoc=PFB_QueryExe(atomicReader , pre_DocN);

			// 后续处理
			Arrays.sort(compact_score_arrayKRoc, new ByWeightComparator());
			int max_resultCRoc = Math.min(maxResults, compact_score_arrayKRoc.length);
			ScoreDoc[] score_docCRoc = new ScoreDoc[max_resultCRoc];
			System.arraycopy(compact_score_arrayKRoc, 0, score_docCRoc, 0, max_resultCRoc);
			TopDocs tdCRoc = new TopDocs(max_resultCRoc, score_docCRoc, (float) score_docCRoc[0].score);
			statsCRoc[i] = analyzeQueryResults(qualityQueries[i], query, tdCRoc, judge, qualityLogCRoc, 1);
			//submitRepCRTER2.report(qualityQueries[i], tdCRTER2, docNameField, searcher);
			//submitRepCRTER2.flush();
		}

		QualityStats avgKRoc = QualityStats.average(statsCRoc);
		avgKRoc.log("SUMMARY", 2, qualityLogCRoc, "  ");
	}

	/** Analyze/judge results for a single quality query; optionally log them. **/
	private QualityStats analyzeQueryResults(QualityQuery qq, Query q, TopDocs td, Judge judge, PrintWriter logger, long searchTime) throws IOException {
		QualityStats stts = new QualityStats(judge.maxRecall(qq), searchTime);
		long t1 = System.currentTimeMillis();	// extraction of first doc name we measure also construction of doc name extractor, just in case.
		ScoreDoc[] scoreDocs = td.scoreDocs;
		DocNameExtractor xt = new DocNameExtractor(docNameField);
		for (int i = 0; i < scoreDocs.length; i++) {
			String docName = xt.docName(searcher, scoreDocs[i].doc);	// scoreDocs[0].doc --> AP900925-0240
			long docNameExtractTime = System.currentTimeMillis() - t1;
			t1 = System.currentTimeMillis();
			boolean isRelevant = judge.isRelevant(docName, qq);		// qq:queryID = 051, isRelevant = true
			stts.addResult(i + 1, isRelevant, docNameExtractTime);
		}
		if (logger != null) {
			logger.println(qq.getQueryID() + "  -  " + q);
			stts.log(qq.getQueryID() + " Stats:", 1, logger, "  ");
		}
		return stts;
	}
	
	/** QueryExe 进行第一次正常查询
	 * @throws IOException **/
	public ScoreDoc[] QueryExe(Set<Integer> doc_set,ArrayList<Term> term_list,int[][] freq_array,JSONArray jsonArray,int index) throws IOException{
		int kk = 0;	
		ScoreDoc[] compact_score_array=new ScoreDoc[doc_set.size()];
//		for (int j = 0; j < numDocs; j++) {                                     // numDocs=有效文档总数78305，循环78305次
//yan			if (doc_set.contains(j)) {                                          // 如果doc_set集合包含了与该查询的所有相关文档的编号，如果它包含第j篇文档，说明相关，则开始计算  BM25算法，doc_set存放了与该查询所有有关的文档编号
//				double total_score = 0.0f;                                      // 定义相关性得分
//				int doc_length = doc_length_map.get(j);                         // 获得第j篇文档的长度
//				double K = k1 * ((1 - b) + b * doc_length / avg_doc_length);    // BM25中的分母中的一部分
//				for (int k = 0; k < term_list.size(); k++) {
//					String termText = term_list.get(k).text();
//					double tf = freq_array[k][j];
//					Integer dfo = term_doc_freq_map.get(termText);
//					double df = (dfo == null) ? 0 : dfo;
//					double TF = (k1 + 1) * tf / (K + tf);
//					double IDF = log2((numDocs - df+ 0.5) / (df+ 0.5));
//					total_score += TF * IDF;
//				}  
//雪颜add                                                                         //////////////////////////////
			JSONObject jsonObject = jsonArray.getJSONObject(index);
          
            Set<String> kvs = jsonObject.keySet();
            for (String key : kvs) {
                String ids0 = jsonObject.getString(key);
                String[] ids = ids0.split(",");
                int[] idsInt = new int[ids.length];
                int count = 0;
                for (String id : ids) {
                    idsInt[count] = Integer.valueOf(id);  //idsInt数组存放文档ID号
                
                    compact_score_array[kk++] = new ScoreDoc(idsInt[count] , 0);   // 得到该查询与doc_set中个的一个文档的得分，kk等于与该查询相关的文档数，计算剩下的doc_set.size()-1个相关文档的得分
                    count+=count;
                }
		}
//		Arrays.sort(compact_score_array, new ByWeightComparator());             // 按重写的排序方法进行排序（从大到小的顺序-Float.compare(a, b);），比较两个ScoreDoc的score值（float型）   
		return compact_score_array;
	}
	
	/** PFB_QueryExe 根据相关反馈进行第二次查询，得到排好顺序的文档得分数组  **/
	public ScoreDoc[] PFB_QueryExe(AtomicReader atomicReader ,HashMap<String,Double>  pre_DocN) throws IOException{
		int k=0;
		int[][] freq_array = new int[pre_DocN.size()][reader.numDocs()];
		Set<Integer> doc_set = new HashSet<Integer>();
		ArrayList<String> query_list = new ArrayList<String>(); 
		for(Entry<String,Double> pre : pre_DocN.entrySet()){
			Term term = new Term(docContentField,pre.getKey());
			query_list.add(pre.getKey());
//			processedQueriesWriter.write(termText+" ");                             // 将每个查询的词条写入文档的一行
			DocsEnum docsEnum = atomicReader.termDocsEnum(term);	                // 某个词条的按文档的倒排索引 例如  word-》1-》3-》4... word代表查询的词条，1,3,4代表出现该词的文档
			while ((docsEnum.nextDoc()) != DocIdSetIterator.NO_MORE_DOCS) {
				int doc_id = docsEnum.docID();                                      // 某个词条的在某个文档中出现
				doc_set.add(doc_id);                                                // 将这个出现该词的文档的编号存放在doc_set中
				freq_array[k][doc_id] = docsEnum.freq();                            // 某个词条的在某个文档中出现的次数
			}
			k++;
		}
		
		int kk = 0;
		ScoreDoc[] compact_score_array=new ScoreDoc[doc_set.size()];
		for (int j = 0; j < numDocs; j++) {                                         // numDocs=有效文档总数78305，循环78305次
			if (doc_set.contains(j)) {                                              // 如果doc_set集合包含了与该查询的所有相关文档的编号，如果它包含第j篇文档，说明相关，则开始计算  BM25算法，doc_set存放了与该查询所有有关的文档编号
				double total_score = 0.0f;                                          // 定义相关性得分
				int doc_length = doc_length_map.get(j);                             // 获得第j篇文档的长度
				double K = k1 * ((1 - b) + b * doc_length / avg_doc_length);        // BM25中的分母中的一部分
				for (int i = 0; i < query_list.size(); i++) {                       // query_list某一某查询词条列表
					double qtf=pre_DocN.get(query_list.get(i));
					int df = term_doc_freq_map.get(query_list.get(i));              // query_list.get(i)求出该词条，然后再从map中取出df
					double tf = freq_array[i][j];                                   // freq_array[i][j] 存放某个查询的第k个词条在第j文档中出现的次数 ，第一个查询有2行，78305列数据。				
					double TF = (k1 + 1) * tf / (K + tf);                           // 这里调用了K
					double IDF = log2((numDocs - df + 0.5) / (df + 0.5));           // 由上面的  df 得到   // 下一行：第一次不能将tf变TF，否则效果差
					total_score += TF * IDF*qtf;                                    // 将所有的该（大循环的第i个）查询的词条的得分都加起来，得到该个查询与第j篇文档的相关性总分
				}   
			compact_score_array[kk++] = new ScoreDoc(j, (float) total_score);       // 得到该查询与doc_set中个的一个文档的得分，kk等于与该查询相关的文档数，计算剩下的doc_set.size()-1个相关文档的得分
			}
		}
		Arrays.sort(compact_score_array, new ByWeightComparator());                 // 按重写的排序方法进行排序（从大到小的顺序-Float.compare(a, b);），比较两个ScoreDoc的score值（float型）   
		return compact_score_array;
	}
	
	/** addVecter 将2个向量按照alpha,beta的倍数合并**/
	public HashMap<String,Double> addVecter(HashMap<String,Double> A, HashMap<String,Double> B,double alpha,double beta) throws Exception {
		HashMap<String,Double> C=new HashMap<String,Double>();
		for(Entry<String,Double> a : A.entrySet())
		{
			if(B.containsKey(a.getKey()))
			{	
				if(a.getValue()*alpha+B.get(a.getKey())*beta!=0)
				C.put(a.getKey(), (a.getValue()*alpha+B.get(a.getKey())*beta));
			}
			else 
//				if(a.getValue()*alpha!=0)
				C.put(a.getKey(), a.getValue()*alpha);			
		}
		for(Entry<String,Double> b : B.entrySet())
		{
			if(!C.containsKey(b.getKey()))
			{		
//				if(b.getValue()*beta!=0)
				C.put(b.getKey(), b.getValue()*beta);
			}					
		}
		return C;
	}
	
	/** 功能函数, 将Vecter排序并返回前n的元素组成的map**/
	public HashMap<String, Double> sortVecter1(HashMap<String,Double> A)  {
		List<HashMap.Entry<String,Double>> list = new ArrayList<HashMap.Entry<String,Double>>(A.entrySet());
		Collections.sort(list,new Comparator<HashMap.Entry<String,Double>>() {
            public int compare(Entry<String, Double> o1,
                    Entry<String, Double> o2) {
                return (o1.getValue().compareTo(o2.getValue()))*-1; //降序排序
            }
		});
		int min=Math.min(N1, list.size());
		HashMap<String,Double> C=new HashMap<String,Double>();
    	double dmax = list.get(0).getValue();
    	//double dmin = list.get(min-1).getValue();
		for(int i=0;i<min;i++)  // 除以间距的归一化
		{
			//if (dmin == dmax || Double.isNaN(dmin) || Double.isNaN(dmax)){
			if (Double.isNaN(dmax)){
				C.put(list.get(i).getKey(), 0.0);	
			}else{
				//C.put(list.get(i).getKey(), (list.get(i).getValue()-dmin)/(dmax-dmin));
				C.put(list.get(i).getKey(), list.get(i).getValue()/dmax);
			}
		} 
		return C;
	}
	
	/** 功能函数, 将Vecter排序并返回前n的元素组成的map**/
	public HashMap<String, Double> sortVecter2(HashMap<String,Double> A)  {
		List<HashMap.Entry<String,Double>> list = new ArrayList<HashMap.Entry<String,Double>>(A.entrySet());
		Collections.sort(list,new Comparator<HashMap.Entry<String,Double>>() {
            //降序排序
            public int compare(Entry<String, Double> o1,
                    Entry<String, Double> o2) {
                return (o1.getValue().compareTo(o2.getValue()))*-1;
            }
		});
		
		HashMap<String,Double> C=new HashMap<String,Double>();
		int min=Math.min(N1, list.size());
		double sum=0.0;
		for(int i=0;i<min;i++) 
		{
			sum+=list.get(i).getValue()*list.get(i).getValue();
		}
		sum=Math.sqrt(sum);
		for(int i=0;i<min;i++)  // 除以平方的和的开方的归一化
		{
			C.put(list.get(i).getKey(), list.get(i).getValue()/sum);  
		}    
		return C;
	}
	
	/** 功能函数, 将Vecter排序并返回前n的元素组成的map**/
	public HashMap<String, Double> sortVecter3(HashMap<String,Double> A)  {
		return sortVecter2(sortVecter1(A));
	}
	
	/** 功能函数, 将Vecter排序并返回前n的元素组成的map**/
	public HashMap<String, Double> sortVecter(HashMap<String,Double> A)  {
		List<HashMap.Entry<String,Double>> list = new ArrayList<HashMap.Entry<String,Double>>(A.entrySet());
		Collections.sort(list,new Comparator<HashMap.Entry<String,Double>>() {
            //降序排序
            public int compare(Entry<String, Double> o1,
                    Entry<String, Double> o2) {
                return (o1.getValue().compareTo(o2.getValue()))*-1;
            }
		});
		HashMap<String,Double> C=new HashMap<String,Double>();
		
		int min=Math.min(N1, list.size());
		for(int i=0;i<min;i++)
		{
			 C.put(list.get(i).getKey(), list.get(i).getValue());			
		}
		
		return C;
	}
	
	/** log2() 实现 **/
	public static double log2(double n) {
		return (Math.log(n) / Math.log(2));
	}
	
	/** round() 实现 **/
	public static double round(double n) {
		return (Math.round(n*100)/100.0);
	}
	
	/** norm() 实现 **/
	public static double norm(double n) {
		return (n/(1.0+n));
	}
}

