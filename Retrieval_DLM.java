package sigir;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
//import java.text.Format;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.lucene.benchmark.quality.Judge;
import org.apache.lucene.benchmark.quality.QualityQuery;
import org.apache.lucene.benchmark.quality.QualityQueryParser;
import org.apache.lucene.benchmark.quality.trec.TrecJudge;
import org.apache.lucene.benchmark.quality.trec.TrecTopicsReader;
import org.apache.lucene.benchmark.quality.utils.DocNameExtractor;
import org.apache.lucene.benchmark.quality.utils.SubmissionReport;
import org.apache.lucene.index.AtomicReader;
import org.apache.lucene.index.DirectoryReader;
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

public class Retrieval_DLM {                                                     // 编译环境Eclipse的字符集和本文编码统一为UTF-8

	public static double alpha=0.55;                                                 // 本方法中第一次查询后的第一部分参数 aphla
	public static int N = 10;                                                       // 本方法中第一次查询后的取前N篇文档参数 N
	public static int N1 = 30;                                                      // 本方法中第一次查询后的取前N1个最大的词作为扩展查询词 
	public static int mu = 2000;                                                    // 本方法中第一次查询后的取前N1个最大的词作为扩展查询词 

//	public static String topic="topics.disk45.301-450";                             // 大家统一用的标准   查询  共有50个，本算法主要用到了<title>内容作为查询词
//	public static String qrels="qrels.disk45.301-450";                              // 人工标注的结果集，指出了上面50个查询于所有文章的相关和不相关性
//	public static String index="index_disk45_stem";                                 // 这个是一个文件夹目录里面存放了建好的索引文件
	public static String result="";                                // 这个文件是该算法运行后生成的，它的内容是按各个指标的统计结果。
	public static String report="";                            // 这个文件是该算法运行后生成的，它的内容是和每个查询相关的前1000篇文档。
//	public static String[] topics={"topics/topics.AP90.51-100","topics/topics.AP8889.51-100","topics/topics.disk12.51-200","topics/topics.disk45.301-450","topics/topics.wt2g","topics/topics.wt10g","topics/topics.FT.301-400","topics/topics.FBIS.351-450","topics/topics.LA.301-400","topics/topics.SJMN.51-150","topics/topics.WSJ.151-200"}; 
//	public static String[] qrels={"qrels/qrels.AP90.51-100","qrels/qrels.AP8889.51-100","qrels/qrels.disk12.51-200","qrels/qrels.disk45.301-450","qrels/qrels.wt2g","qrels/qrels.wt10g","qrels/qrels.FT.301-400","qrels/qrels.FBIS.351-450","qrels/qrels.LA.301-400","qrels/qrels.SJMN.51-150","qrels/qrels.WSJ.151-200"}; 
//	public static String[] index={"index_AP90","index_AP8889","index_disk12","index_disk45","index_WT2G","index_WT10G","index_FT","index_FBIS","index_LA","index_SJMN","index_WSJ"}; 
//	public static String[] dataName={"AP90_DLM","AP8889_DLM","disk12_DLM","disk45_DLM","WT2G_DLM","WT10G_DLM","FT_DLM","FBIS_DLM","LA_DLM","SJMN_DLM","WSJ_DLM"};
	
	public static String[] topics={"topics/topics.AP89.1-50","topics/topics.AP8889.101-150","topics/topics.AP8889.151-200","topics/topics.disk45.301-450","topics/topics.wt2g","topics/topics.wt10g","topics/topics.FT.301-400","topics/topics.FBIS.351-450","topics/topics.LA.301-400","topics/topics.SJMN.51-150","topics/topics.WSJ.151-200"}; 
	public static String[] qrels={"qrels/qrels.AP89.1-50","qrels/qrels.AP8889.101-150","qrels/qrels.AP8889.151-200","qrels/qrels.disk45.301-450","qrels/qrels.wt2g","qrels/qrels.wt10g","qrels/qrels.FT.301-400","qrels/qrels.FBIS.351-450","qrels/qrels.LA.301-400","qrels/qrels.SJMN.51-150","qrels/qrels.WSJ.151-200"}; 
	public static String[] index={"index_AP89","index_AP8889","index_AP8889","index_disk45","index_WT2G","index_WT10G","index_FT","index_FBIS","index_LA","index_SJMN","index_WSJ"}; 
	public static String[] dataName={"1AP89_DLM","2AP8889_DLM","3AP8889_DLMM","disk45_DLM","WT2G_DLM","WT10G_DLM","FT_DLM","FBIS_DLM","LA_DLM","SJMN_DLM","WSJ_DLM"};
	
	String docNameField = "docno";	                                                // 文件编号
	String docContentField = "contents";                                            // 文件内容，为content或者text
	
	int numDocs;
	int maxResults = 1000;
	long total_term_freq = 0;                                                       // 所有词条和它的在所有文档中的出现次数tf
	double avg_doc_length=0.0;                                                      // average of document length
	
	QualityQuery[] qualityQueries;	
	QualityQueryParser qqParser;	                                                // Parse a QualityQuery into a Lucene query.
	IndexReader reader;	
	IndexSearcher searcher;			
	PrintWriter qualityLog;	
	SubmissionReport submitRep;	
	Judge judge;	
	
	
	
	HashMap<String, Long> term_total_freq_map = new HashMap<String, Long>();		// term frequency in collection(TF) 每一个词条和它的在所有文档中的出现次数cf
	HashMap<String, Integer> term_doc_freq_map = new HashMap<String, Integer>();	// term frequency in a document(DF) 每一个词条和出现它文章的总数df	
	HashMap<Integer, Integer> doc_length_map = new HashMap<Integer, Integer>();		// document length  每个文档的长度dl
	HashMap<Integer, Double> doc_avg_tf_map = new HashMap<Integer, Double>();       // average of term frequency in a document 保存该文档的所有词的平均出现次数atf

	/** 代码步骤0，直接调用核心算法LM**/
	public static void main(String[] args) throws Exception{
		Param_Test();
	}
	
	
	/** 代码步骤1，四种参数的循环设置，便于测试分析各个参数的表现**/
	public static void Param_Test() throws Exception {
		for (int i = 4; i <= 4; i++){
			for (N1 = 10; N1 <= 10; N1 += 10) {
				if(N1==40) continue;
//				switch(i)
//				{
//					case 0:mu=600;if(N1==10) {alpha=0.7;}if(N1==20) {alpha=0.7;}if(N1==30) {alpha=0.8;}if(N1==50) {alpha=0.8;}break;
//					case 1:mu=750;if(N1==10) {alpha=0.5;}if(N1==20) {alpha=0.7;}if(N1==30) {alpha=0.6;}if(N1==50) {alpha=0.7;}break;
//					case 2:mu=850;if(N1==10) {alpha=0.5;}if(N1==20) {alpha=0.7;}if(N1==30) {alpha=0.7;}if(N1==50) {alpha=0.7;}break;
//					case 3:mu=300;if(N1==10) {alpha=0.6;}if(N1==20) {alpha=0.6;}if(N1==30) {alpha=0.7;}if(N1==50) {alpha=0.7;}break;
//					case 4:mu=1400;if(N1==10) {alpha=0.3;}if(N1==20) {alpha=0.4;}if(N1==30) {alpha=0.5;}if(N1==50) {alpha=0.5;}break;
//					case 5:mu=1600;if(N1==10) {alpha=0.4;}if(N1==20) {alpha=0.3;}if(N1==30) {alpha=0.4;}if(N1==50) {alpha=0.4;}break;
//					case 6:mu=1450;if(N1==10) {alpha=0.8;}if(N1==20) {alpha=0.3;}if(N1==30) {alpha=0.4;}if(N1==50) {alpha=0.4;}break;
//					case 7:mu=350;if(N1==10) {alpha=0.5;}if(N1==20) {alpha=0.3;}if(N1==30) {alpha=0.4;}if(N1==50) {alpha=0.4;}break;
//					case 8:mu=850;if(N1==10) {alpha=0.6;}if(N1==20) {alpha=0.3;}if(N1==30) {alpha=0.4;}if(N1==50) {alpha=0.4;}break;
//					case 9:mu=350;if(N1==10) {alpha=0.8;}if(N1==20) {alpha=0.3;}if(N1==30) {alpha=0.4;}if(N1==50) {alpha=0.4;}break;
//					case 10:mu=1200;if(N1==10) {alpha=0.7;}if(N1==20) {alpha=0.3;}if(N1==30) {alpha=0.4;}if(N1==50) {alpha=0.4;}break;
//					
//				}
				for(alpha=0.0;alpha<=0.0;alpha=Math.round((alpha+0.1)*10.0)/10.0)
				{//alpha=Math.round(alpha*10.0)/10.0;
					Param_Name(N, N1, alpha, i);                                // 处理输出的参数文件名，接着调用核心函数开始计算
					new Retrieval_DLM().RunLM_PFB(topics[i], qrels[i], index[i], result, report);
				}
			}
		}
	}


	/** 代码步骤1.1，处理存放结果的2个文件名，都存放在result文件夹内**/
	public static void Param_Name(int N, int N1, double alpha,int i) {
		StringBuffer Name = new StringBuffer("result/DLM/s/");
		Name.append(dataName[i]).append("_mu_").append(String.format("%d", mu)).append("_N_").append(String.format("%2d", N));
		Name.append("_N1_").append(String.format("%2d", N1)).append("_alpha_").append(String.format("%.2f", alpha));
		StringBuffer Name1 = new StringBuffer(Name);
		result = String.valueOf(Name.append("_p1.txt"));
		report = String.valueOf(Name1.append("_report.txt"));
		System.out.println(result);                                                // 输出结果文件名
	}
	
	/** 代码步骤1.2，核心算法LM(初始化和对索引的处理),各个参数含义 见最上面的static定义**/
	public void RunLM_PFB(String topicFile, String qrelsFile, String indexFile, String resultFile, String reportFile) throws Exception {
		System.out.println("RunLM_PFB...");
		Directory directory = FSDirectory.open(new File(indexFile));                // 打开磁盘已建好的索引
		reader = DirectoryReader.open(directory);                                   // IndexReader
		searcher = new IndexSearcher(reader);                                       // IndexSearcher
		docNameField = "docno";                                                     // 文档名
		docContentField = "contents";                                               // 文档题目和内容，contents=title+text
		qualityLog = new PrintWriter(new File(resultFile), "UTF-8");                // 创建文件写入流AP90-BM25.txt，准备写入结果文件(包括文件丢失信息和每个查询的各项统计指标)，以utf-8的方式
		TrecTopicsReader qReader = new TrecTopicsReader();	                        // #1  定义内容读取器（benchmark自带）
		qualityQueries = qReader.readQueries(new BufferedReader(new FileReader(new File(topicFile))));	// #1 Read TREC topics as QualityQuery[],#1 将标准查询内容（topics.51-100 ）的内容按标签一对对的读取到qualityQueries[]数组中（按标签读取）,(queryID，HashMap<标签,内容>)
	                                                                                // 数组中存放了 ID和（title，description，narrative）3个键的键值对
		judge = new TrecJudge(new BufferedReader(new FileReader(new File(qrelsFile))));	// judge得到人工标准的Q与D相关的结果qrels.51-100.disk3，（函数处理了第1列（查询序号），第3列（文档名），第4（是否相关）列
														                            // judge的judgements存储了HashMap<queryID,QRelJudgement>键值对,而QRelJudgement为(queryID，HashMap<docName,docName>)
		judge.validateData(qualityQueries, qualityLog);                             // #3 Verify query and Judge match  验证qualityQueries与judgements的queryID是否对应，
		                                                                            //如果后者缺少对应的queryID人工标注数据会在qualityLog（AP90-BM25.txt）中写入缺失的文件信息
		qqParser = new MyQQParser("title", "contents");                             // #4 Create parser to translate queries into Lucene queries
//		PrintWriter pw=new PrintWriter(new File(reportFile), "UTF-8");              // pan add 将下一句的参数单独拿出来为了更好的关闭
//		submitRep = new SubmissionReport(pw, "TEST");                               // 创建文件写入流AP90-BM25-report.txt，准备写入结果文件(包括每个查询的命中文档的具体得分)，以utf-8的方式
		execute();                                                                  // termStats(); docStats();search(); 执行具体的参数统计和查询search
		directory.close();                                                          // 关闭索引文件目录读取流
		qualityLog.close();                                                         // 关闭统计文件写入流
//		pw.close();                                                                 // pan add 关闭具体结果文件写入流(更加稳定)
	}	
	
	/** 代码步骤1.2.1，依次计算各个参数，然后进行查询**/
	public void execute() throws Exception {
		termStats();
		docStats();
		search();
	}	
	
	/** 代码步骤1.2.1.1，以term的角度来进行处理，求出cf,df,tf**/
	public void termStats() throws Exception {	                                    // directory = FSDirectory.open(new File(indexFile)),indexFile="index_AP90_stem"
		total_term_freq=0;
		Fields fields = MultiFields.getFields(reader);                              // reader(IndexReader) = DirectoryReader.open(directory)
		Terms terms = fields.terms(docContentField);                                // terms 是所有索引文件中"contents"域 的个数 共有78305个，String docContentField = "contents"   
		TermsEnum iterator = terms.iterator(null);                                  // terms.getSumTotalTermFreq(),16322984 是  所有词条（174836个）的词频ctf之和
		BytesRef byteRef = null;
		while ((byteRef = iterator.next()) != null) {                               // 循环执行 174836 次  是所有的词条信息，每次取一条（倒排）
			String text = new String(byteRef.bytes, byteRef.offset, byteRef.length);// 每一个词条的信息
			term_total_freq_map.put(text, iterator.totalTermFreq());                // 每一个词条和它的在所有文档中的出现次数cf			
			term_doc_freq_map.put(text, iterator.docFreq());	                    // 每一个词条和出现它文章的总数df	
			total_term_freq += iterator.totalTermFreq();                            // 所有词条和它的在所有文档中的出现次数tf
		}
	}	

	/** 代码步骤1.2.1.2，以doc的角度来进行处理**/
	public void docStats() throws Exception {	
		long total_dl = 0;
		for (int j = 0; j < reader.numDocs(); j++) {                                // "index_AP90_stem" reader.numDocs()索引中文档总数78305
			int docLen = 0;		
			int term_num = 0;	
			Terms terms = reader.getTermVector(j, docContentField);	                // docContentField="content",getTermVectors(docID).terms("content"),得到某一篇文档content中的倒排词典，第1,2,3,4篇各有259，88，240，156个词条
			if (terms != null && terms.size() > 0) {                                // 如果词典不为空
				TermsEnum termsEnum = terms.iterator(null);		                    // 对词典的每个词进行遍历
				while ((termsEnum.next()) != null) {
					int freq = (int) termsEnum.totalTermFreq();                     // 当前词条在当前文档中的出现次数cf
					docLen += freq;                                                 // 该文档的总词数（长度）
					term_num++;                                                     // 该文档词条的个数 等价于terms.size()
				}
			}
			total_dl += docLen;
			doc_length_map.put(j, docLen);                                          // 保存该文档的长度dl
			double avg_tf = (term_num == 0) ? 0 : ((double) docLen) / term_num;     // 求该文档的所有词的平均出现次数atf  
			doc_avg_tf_map.put(j, avg_tf);									        // 保存该文档的所有词的平均出现次数atf
		}
		avg_doc_length = ((double) total_dl) / reader.numDocs();                    // 所有文档的平均长度
	}

	/** 代码步骤1.2.1.3，计算各个查询Query与各个文档Doc的得分（核心步骤！）**/
	public void search() throws Exception {
//		FileWriter processedQueriesWriter = new FileWriter("processedresult/AP90_processedQueries"); 
		                                                                            // 构建文件输出流，产生一个文档用来存放所有的query，一行一条，共50行
		AtomicReader atomicReader = SlowCompositeReaderWrapper.wrap(reader);        // fields = MultiFields.getFields(reader);liveDocs = MultiFields.getLiveDocs(reader)
		QualityStats stats[] = new QualityStats[qualityQueries.length];             // stats为存放各个查询统计结果的数组，qualityQueries=》(queryID，HashMap<标签,内容>) 50个
		for (int i = 0; i < qualityQueries.length; i++) {                           // 对每一个查询做出如下处理
			QualityQuery qq = qualityQueries[i];                                    // 获得上面读取好的 50条查询信息
			Query query = qqParser.parse(qq);	                                    // 构建query查询对象,System.err.println(qq.getQueryID()+qq.getValue("title"));  打印qq数组中一个元素的ID和1个键值对 
			HashSet<Term> term_set = new HashSet<Term>();                           // 构建一个词典set
			query.extractTerms(term_set);	                                        // 将每一个query 进行词条化然后将结果存放在 term_set中，term_set种就是一个查询的几个分词
			ArrayList<Term> term_list = new ArrayList<Term>();                      
			for (Term term : term_set) {                                            // term 为 term_set 中的每个词条，是某一查询词条
				DocsEnum docsEnum = atomicReader.termDocsEnum(term);
				if(docsEnum!=null)
				term_list.add(term);                                                // 将词条从 term_set取出存放在term_list中
			}
			Set<Integer> doc_set = new HashSet<Integer>();	
			int[][] freq_array = new int[term_list.size()][reader.numDocs()];       // 构建一个二维数组有 词条的数目行（第一个查询2行），有78305列，存放每个词条在每个文档中出现的次数

			for (int k = 0; k < term_list.size(); k++) {
				Term term = term_list.get(k);
//				processedQueriesWriter.write(termText+" ");                         // 将每个查询的词条写入文档的一行
				DocsEnum docsEnum = atomicReader.termDocsEnum(term);	            // 某个词条的按文档的倒排索引 例如  word-》1-》3-》4... word代表查询的词条，1,3,4代表出现该词的文档
				while ((docsEnum.nextDoc()) != DocIdSetIterator.NO_MORE_DOCS) {
					int doc_id = docsEnum.docID();                                  // 某个词条的在某个文档中出现
					//System.err.println("doc_id big = "+doc_id);
					doc_set.add(doc_id);                                            // 将这个出现该词的文档的编号存放在doc_set中
					freq_array[k][doc_id] = docsEnum.freq();                        // 某个词条的在某个文档中出现的次数
				}
			}
//			processedQueriesWriter.write("\r\n");
			numDocs = reader.numDocs();                                             // 获得第文档总数N
			
			HashMap<String,Double> q_Doc=new HashMap<String,Double>();
			for(Term t:term_list)              
			{
				q_Doc.put(t.text(), (1.0)/term_list.size());                          // q0规范化处理                                      //将查询的词条以权重1放入新的文档向量q_Doc中
			}
			
			/** 进行第一次查询 ，得到根据文档得分排好顺序的文档数组，调用函数1.2.1.3.1**/
			ScoreDoc[] compact_score_array=QueryExe(doc_set,term_list,freq_array,q_Doc);  
		
			/** 进行后续的结果统计，调用函数1.2.1.3.3 **/ 
			CreateResult(compact_score_array,qualityQueries,i,query,stats);
		}
		WriteResult(stats);                                                         // 将总的结果统计写入文件      
	}
	
	/** 功能函数, 将2个向量合并,(1-a)*q0 +a*q1 **/
	public HashMap<String,Double> addVecter_alpha(HashMap<String,Double> A, HashMap<String,Double> B) throws Exception {
		HashMap<String,Double> C=new HashMap<String,Double>();
		for(Entry<String,Double> a : A.entrySet())
		{
			if(B.containsKey(a.getKey()))
			{				
				C.put(a.getKey(), ((1-alpha)*a.getValue()+alpha*B.get(a.getKey())));
			}
			else C.put(a.getKey(), (1-alpha)*a.getValue());			
		}
		for(Entry<String,Double> b : B.entrySet())
		{
			if(!C.containsKey(b.getKey()))
			{				
				C.put(b.getKey(), alpha*b.getValue());
			}					
		}
		return C;
	}
	
	/** 代码步骤1.2.1.3.1,进行第一次正常查询**/
	public ScoreDoc[] QueryExe(Set<Integer> doc_set,ArrayList<Term> term_list,int[][] freq_array,HashMap<String,Double> q_Doc){
	//public ScoreDoc[] QueryExe(Set<Integer> doc_set,ArrayList<Term> term_list,int[][] freq_array,HashMap<String,Double> q_Doc){
		int kk = 0;	
		ScoreDoc[] compact_score_array=new ScoreDoc[doc_set.size()];
		for (int j = 0; j < numDocs; j++) {                                         // numDocs=有效文档总数78305，循环78305次
			if (doc_set.contains(j)) {                                              // 如果doc_set集合包含了与该查询的所有相关文档的编号，如果它包含第j篇文档，说明相关，则开始计算  BM25算法，doc_set存放了与该查询所有有关的文档编号
				double total_score = 0.0;                                           // 定义相关性得分
				
				int dl = doc_length_map.get(j);                                     // 获得第j篇文档的长度
				for (int k = 0; k < term_list.size(); k++) {                        // term_list某一某查询词条列表
					//double qtf=q_Doc.get(term_list.get(k).text());
					//System.out.println("qtf="+qtf);					
					Long ctf= term_total_freq_map.get(term_list.get(k).text());     // 某个词在全部文档中出现的次数 
					double tf = freq_array[k][j];	                                // freq_array[k][j] 存放某个查询的第k个词条在第j文档中出现的次数 ，第一个查询有2行，78305列数据。				
					//System.out.println(tf+"  "+dl+"  "+ctf+"  "+total_term_freq);
					total_score+=log2((1.0*tf/(dl+mu)+1.0*mu/(dl+mu)*ctf/total_term_freq)); 
					                                                                // 将所有的该（大循环的第i个）查询的词条的得分都连乘起来，得到该个查询与第j篇文档的相关性总分
				} 
				//System.err.println(String.format("%.20f",total_score));
			compact_score_array[kk++] = new ScoreDoc(j, (float) total_score);       // 得到该查询与doc_set中个的一个文档的得分，kk等于与该查询相关的文档数，计算剩下的doc_set.size()-1个相关文档的得分
			}
		}
		Arrays.sort(compact_score_array, new ByWeightComparator());                 // 按重写的排序方法进行排序（从大到小的顺序-Float.compare(a, b);），比较两个ScoreDoc的score值（float型）   
		return compact_score_array;
	}
	                                                                                                                                                                                        
	/** Pan伪相关反馈，用新的q1再次进行检索求得结果 **/
	/** 代码步骤1.2.1.3.2,核心步骤：根据相关反馈进行第二次查询，得到排好顺序的文档得分数组 **/
	public ScoreDoc[] PFB_QueryExe(AtomicReader atomicReader ,HashMap<String,Double>  pre_DocN) throws IOException{
		int k=0;
		int[][] freq_array = new int[pre_DocN.size()][reader.numDocs()];
		Set<Integer> doc_set = new HashSet<Integer>();
		ArrayList<String> query_list = new ArrayList<String>(); 
		for(Entry<String,Double> pre : pre_DocN.entrySet()){
			Term term = new Term(docContentField,pre.getKey());
			query_list.add(pre.getKey());
			//processedQueriesWriter.write(termText+" ");                           // 将每个查询的词条写入文档的一行
			DocsEnum docsEnum = atomicReader.termDocsEnum(term);	                // 重要语句！某个词条的按文档的倒排索引 例如  word-》1-》3-》4... word代表查询的词条，1,3,4代表出现该词的文档
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
				double total_score = 0.0;                                           // 定义相关性得分
				int dl = doc_length_map.get(j);
				for (int i = 0; i < query_list.size(); i++) {                       // query_list某一某查询词条列表
					double qtf=pre_DocN.get(query_list.get(i));
					Long ctf= term_total_freq_map.get(query_list.get(i));
					double tf = freq_array[i][j];                                   // freq_array[i][j] 存放某个查询的第k个词条在第j文档中出现的次数 ，第一个查询有2行，78305列数据。				
					//Double s_temp=log2(1.0*tf/(dl+mu)+1.0*mu/(dl+mu)*ctf/total_term_freq);
					total_score +=log2(1.0*tf/(dl+mu)+1.0*mu/(dl+mu)*ctf/total_term_freq)*qtf;     
					//System.err.println("log="+s_temp+"||||||||qtf="+qtf);
				}  
				//System.err.println(String.format("%.20f",(double) (total_score*1E150)));
			compact_score_array[kk++] = new ScoreDoc(j, (float) (total_score));     // 得到该查询与doc_set中个的一个文档的得分，kk等于与该查询相关的文档数，计算剩下的doc_set.size()-1个相关文档的得分
			}
		}
		Arrays.sort(compact_score_array, new ByWeightComparator());                 // 按重写的排序方法进行排序（从大到小的顺序-Float.compare(a, b);），比较两个ScoreDoc的score值（float型）   
		return compact_score_array;
	}
	
	/** 功能函数, 将Vecter排序并返回前n的元素组成的map**/
	public HashMap<String, Double> sortVecter(HashMap<String,Double> A)  {
		List<HashMap.Entry<String,Double>> list = new ArrayList<HashMap.Entry<String,Double>>(A.entrySet());
		Collections.sort(list,new Comparator<HashMap.Entry<String,Double>>() {
            //降序排序
            public int compare(Entry<String, Double> o1,
                    Entry<String, Double> o2) {
                 return (o1.getValue().compareTo(o2.getValue()))*-1;                // 从大到小 排序，要从小到大的话将-1改为1即可               
            }
		});
		
		HashMap<String,Double> C=new HashMap<String,Double>();
		double sum=0.0;
		for(int i=0;i<N1;i++)
		{
			sum+= list.get(i).getValue();	                                        // 对list中所有的term的得分求和		
		}
		for(int i=0;i<N1;i++)
		{
			if(sum==0)  
			{
				C.put(list.get(i).getKey(), 0.0);	            	
			}
			else 
			{
				C.put(list.get(i).getKey(), list.get(i).getValue()/sum);	            // 对每个term的得分规范化处理		
				
				//System.err.println(list.get(i).getValue()/sum);
			}
			
			
			//System.err.println(sum);
			
		}
		
		return C;
	}
	
	
	
	/** 功能函数, 将2个向量合并**/
	public HashMap<String,Double> addVecter(HashMap<String,Double> A, HashMap<String,Double> B) throws Exception {
		HashMap<String,Double> C=new HashMap<String,Double>();
		for(Entry<String,Double> a : A.entrySet())
		{
			if(B.containsKey(a.getKey()))
			{				
				C.put(a.getKey(), (a.getValue()+B.get(a.getKey())));
			}
			else C.put(a.getKey(), a.getValue());			
		}
		for(Entry<String,Double> b : B.entrySet())
		{
			if(!C.containsKey(b.getKey()))
			{				
				C.put(b.getKey(), b.getValue());
			}					
		}
		return C;
	}
	
	/** 代码步骤1.2.1.3.3,进行后续的结果统计**/
	public void CreateResult(ScoreDoc[] compact_score_array1,QualityQuery[] qualityQueries,int i,Query query,QualityStats[] stats) throws IOException{
		int max_result = Math.min(maxResults, compact_score_array1.length);
		ScoreDoc[] score_doc = new ScoreDoc[max_result];
		System.arraycopy(compact_score_array1, 0, score_doc, 0, max_result);	    // 硬拷贝要求大小的相关得分，// 下一句：构建TopDocs，它有3要素 （总数、得分数组地址、最大得分）		
		TopDocs td = new TopDocs(max_result, score_doc, (float) score_doc[0].score);  
		stats[i] = analyzeQueryResults(qualityQueries[i], query, td, judge, qualityLog, 1);  
	}
	
	/** 代码步骤1.2.1.3.3.1，统计结果中的各项指标的值**/
	private QualityStats analyzeQueryResults(QualityQuery qq, Query q, TopDocs td, Judge judge, PrintWriter logger, long searchTime) throws IOException {
		QualityStats stts = new QualityStats(judge.maxRecall(qq), searchTime);
		long t1 = System.currentTimeMillis();	
		ScoreDoc[] scoreDocs = td.scoreDocs;
		DocNameExtractor xt = new DocNameExtractor(docNameField);
		for (int i = 0; i < scoreDocs.length; i++) {
			String docName = xt.docName(searcher, scoreDocs[i].doc);	
			long docNameExtractTime = System.currentTimeMillis() - t1;
			t1 = System.currentTimeMillis();
			boolean isRelevant = judge.isRelevant(docName, qq);		
			stts.addResult(i + 1, isRelevant, docNameExtractTime);
		}
		if (logger != null) {
			logger.println(qq.getQueryID() + "  -  " + q);
			stts.log(qq.getQueryID() + " Stats:", 1, logger, "  ");
		}
		return stts;
	}
	
	/** 代码步骤1.2.1.3.4,写入各个统计结果**/
	public void WriteResult(QualityStats[] stats){
		QualityStats avg = QualityStats.average(stats);		                  
		avg.log("SUMMARY", 2, qualityLog, "  ");
	}
	
	/** 辅助函数, 打印map向量**/
	public void printVecter(HashMap<String,Double> A){
		for(Entry<String,Double> a : A.entrySet())
		{
			System.err.println("name=:"+a.getKey()+" value=:"+a.getValue());
		}
	}
	
	/** log2函数**/
	public static double log2(double n) {
		return (Math.log(n) / Math.log(2));
	}
	
}


