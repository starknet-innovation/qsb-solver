__global__ void compare(uint32_t *a,uint32_t *b,const uint32_t *input,int n){
 int i=blockIdx.x*blockDim.x+threadIdx.x;if(i>=n)return;
 uint32_t x[8],y[8];for(int j=0;j<8;j++)x[j]=y[j]=input[i*8+j];
 baseline::qsb_compress_constant_rolled(x);candidate::qsb_compress_constant_rolled(y);
 for(int j=0;j<8;j++){a[i*8+j]=x[j];b[i*8+j]=y[j];}
}
void reference(uint32_t *s,const uint32_t *w){
 for(int block=0;block<4;block++){
  uint32_t v[8];memcpy(v,s,32);
  for(int r=0;r<64;r++){
   uint32_t t=v[7]+S1(v[4])+Ch(v[4],v[5],v[6])+w[block*64+r];
   uint32_t u=S0(v[0])+Maj(v[0],v[1],v[2]);
   for(int j=7;j>0;j--)v[j]=v[j-1];v[4]+=t;v[0]=t+u;
  }
  for(int j=0;j<8;j++)s[j]+=v[j];
 }
}
int main(){
 const int n=1024;const size_t bytes=n*8*sizeof(uint32_t);
 std::vector<uint32_t> states(n*8),w(256),a(n*8),b(n*8);
 std::mt19937 rng(20260930);for(auto &x:states)x=rng();
 for(int j=0;j<8;j++){states[j]=0;states[8+j]=UINT32_MAX;states[16+j]=1u<<j;}
 uint32_t *ds,*da,*db;CK(cudaMalloc(&ds,bytes));CK(cudaMalloc(&da,bytes));CK(cudaMalloc(&db,bytes));
 CK(cudaMemcpy(ds,states.data(),bytes,cudaMemcpyHostToDevice));
 unsigned checked=0;
 for(int trial=0;trial<10;trial++){
  for(unsigned j=0;j<w.size();j++)w[j]=trial==0?0:trial==1?UINT32_MAX:trial==2?j:rng();
  CK(cudaMemcpyToSymbol(baseline::QSB_CONST_SCHEDULE,w.data(),1024));
  CK(cudaMemcpyToSymbol(candidate::QSB_CONST_SCHEDULE,w.data(),1024));
  compare<<<(n+127)/128,128>>>(da,db,ds,n);CK(cudaGetLastError());CK(cudaDeviceSynchronize());
  CK(cudaMemcpy(a.data(),da,bytes,cudaMemcpyDeviceToHost));CK(cudaMemcpy(b.data(),db,bytes,cudaMemcpyDeviceToHost));
  for(int i=0;i<n;i++){
   uint32_t ref[8];memcpy(ref,states.data()+i*8,32);reference(ref,w.data());
   if(memcmp(ref,a.data()+i*8,32)||memcmp(ref,b.data()+i*8,32)){fprintf(stderr,"Mismatch %d %d\n",trial,i);return 3;}checked++;
  }
 }
 CK(cudaFree(ds));CK(cudaFree(da));CK(cudaFree(db));
 printf("{\"status\":\"passed\",\"nativeCompressionComparisons\":%u,\"blocksPerComparison\":4,\"scope\":\"extracted constant compression only\"}\n",checked);
}
