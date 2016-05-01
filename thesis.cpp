#include <stdio.h>
#include <algorithm>
#include <utility>
#include <memory.h>
#include <math.h>
#include <set>
#include <vector>
#include <stack>
#include <queue>
#define mp make_pair
using namespace std;
const int max_p = 500000;
const double eps1 = 0.01;
const double eps2 = 0.01;
const int divide = 1000;
const double PI = 3.14159265358979;
double dadj = 0.03;
double limit = 0.47;
typedef pair<double,double> pi;
 
int inputsize, pcdsize;
pair<int,int> object[max_p];
bool isobject[max_p], fakestr[max_p];
int cntobj[max_p], cursor[max_p];
vector<double> vx, vy;
 
struct point {
    double x,y,z;
    int tag;
    bool operator <(const point &t) const {
        return y < t.y;
    }
} plist[max_p];
 
struct twodpoint {
    double x,y;
    int tag;
    bool operator <(const twodpoint &t) const {
        return (x == t.x) ? (y < t.y) : (x < t.x);
    }
    bool operator ==(const twodpoint &t) const {
        return (x == t.x) && (y == t.y);
    }
};

struct halfplane {
    double a, b, c;
};

pi cross(halfplane &a, halfplane &b){
    long double det = a.b * b.a - a.a * b.b;
    return pi((double)((long double)(a.c*b.b-a.b*b.c)/det),(double)((long double)(a.a*b.c-a.c*b.a)/det));
}
bool overpi(halfplane &a, halfplane &b) {
    double ang1 = atan2(a.a, -a.b);
    double ang2 = atan2(b.a, -b.b);
    if(ang1 >= 0) {
        if(ang2 <= ang1-PI || ang2 > ang1) return true;
    } else {
        if(ang2 > ang1 && ang2 <= PI+ang1) return true;
    }
    return false;
}
bool out(halfplane &a, halfplane &b, halfplane &c){
    pi crs = cross(a, c);
    double func = b.a * crs.first + b.b * crs.second + b.c;
    if(func >= 1e-2) return true;
    return false;
}
bool inside(halfplane &a, halfplane &b){
    halfplane p;
    p.a = -a.b;
    p.b = a.a;
    p.c = 0;
    pi t = cross(p, a);
    double func = t.first * b.a + t.second * b.b + b.c;
    return func >= 1e-2;
}
void normalize(vector<halfplane> &v){
    vector<halfplane> buf;
    for(auto &i : v){
        if(buf.size() > 0){
            double ang1 = atan2(-buf.back().b, buf.back().a);
            double ang2 = atan2(-i.b, i.a);
            if(fabs(ang2 - ang1) <= 1e-2) {
                if(!inside(buf.back(), i)) {
                    buf.pop_back();
                }
            } else {
                ang1 = atan2(-buf.back().a, buf.back().b);
                ang2 = atan2(-i.a, i.b);
                if(fabs(ang2 - ang1) <= 1e-2) {
                    if(!inside(buf.back(), i)) {
                        buf.pop_back();
                    }
                }
            }
        }
        buf.push_back(i);
    }
    v = buf;
}
double dist(point a,point b) {
    return (a.x-b.x)*(a.x-b.x) + (a.y-b.y)*(a.y-b.y) + (a.z-b.z)*(a.z-b.z);
}
double dist(double a,double b,double c,double d) {
	return (a-b)*(a-b) + (c-d)*(c-d);
}
double dist(double a,double b,double c,point d) {
	return fabs(a*d.x+b*d.y+c) / sqrt(a*a+b*b);
}
bool ccw(twodpoint a,twodpoint b,twodpoint c) {
	return a.x*b.y+b.x*c.y+c.x*a.y-a.x*c.y-b.x*a.y-c.x*b.y > 0;
}
bool ccw(pi a,pi b,pi c) {
    return a.first*b.second+b.first*c.second+c.first*a.second-a.first*c.second-b.first*a.second-c.first*b.second > 0;
}
 
struct segtree {
    multiset<point> tree[(1<<20)-1];
    vector<int> adjpoint[max_p];
    int lim;
    void init(int n) {
        for(lim = 1; lim <= n; lim  <<= 1);
    }
    void query(int ind,double x,double y,double z,int tag) {
        auto head = tree[ind].lower_bound({x, y-dadj, z, tag});
        auto tail = tree[ind].lower_bound({x, y+dadj, z, tag});
        while(head != tail) {
            if(dist(*head, {x,y,z,tag}) < dadj * dadj) {
                adjpoint[tag].push_back((*head).tag);
                adjpoint[(*head).tag].push_back(tag);
            }
            head ++;
        }
        return;
    }
    void add(double x,double y,double z,int tag) {
        int op = (int)(lower_bound(vx.begin(), vx.end(), x-dadj) - vx.begin()) + lim;
        int ed = (int)(lower_bound(vx.begin(), vx.end(), x+dadj) - vx.begin()) + lim;
        while(op<ed) {
            if(op&1) query(op++, x,y,z,tag);
            if(!(ed&1)) query(ed--, x,y,z,tag);
            op >>= 1;
            ed >>= 1;
        }
        if(op == ed) query(op, x,y,z,tag);
        int t = (int)(lower_bound(vx.begin(), vx.end(), x) - vx.begin());
        for(int ind=t+lim; ind ; ind >>= 1) {
            tree[ind].insert({x,y,z,tag});
        }
        return;
    }
    void del(double x,double y,double z,int tag) {
        int t = (int)(lower_bound(vx.begin(), vx.end(), x) - vx.begin());
        for(int ind=t+lim; ind ; ind >>= 1) {
            tree[ind].erase(tree[ind].find({x,y,z,tag}));
        }
        return;
    }
} seg;

struct planework {
	twodpoint temp[max_p];
    vector<int> clist;
    vector<halfplane> hp;
    vector<twodpoint> inconvex;
	int planesize;

	void init(double deg) {
		planesize = 0;
        clist.clear();
        hp.clear();
        inconvex.clear();
		double cx = vx[(int)vx.size()/2], cy = vy[(int)vy.size()/2];
		double a = tan(deg), b = -1.0, c = -cx * tan(deg) + cy;
		for(int i=0;i<inputsize;i++) {
			double l = dist(a,b,c,plist[i]);
			if(l < eps1) {
				double origin_point = dist(cx,cy,plist[i].x,plist[i].y);
                double A = sqrt(origin_point-l*l);
                double B = plist[i].z;
                int C = plist[i].tag;
				if(a*plist[i].x+b*plist[i].y+c > 0) {
                    twodpoint newp = {A,B,C};
                    if(planesize>0 && temp[planesize-1] == newp) continue;
                    temp[planesize++] = newp;
                } else {
                    twodpoint newp = {-A,B,C};
                    if(planesize>0 && temp[planesize-1] == newp) continue;
                    temp[planesize++] = newp;
                }
			}
		}
		sort(temp, temp+planesize);
		sort(temp+1, temp+planesize, [&](const twodpoint &a, const twodpoint &b) {
			return atan2(a.y-temp[0].y,a.x-temp[0].x) > atan2(b.y-temp[0].y,b.x-temp[0].x); 
		});
		return;
	}

	void error_tolerant_convex_hull() {
		grahamscan();
		half_plane_intersection();
		return;
	}

    void grahamscan() {
        if(planesize < 2) return;
        vector<int> pl(10000);
        pl.push_back(0);
        pl.push_back(1);
        int last = 1;
        for(int i=2; i<planesize;i++) {
            while(last > 0 && ccw(temp[pl[last-1]], temp[pl[last]], temp[i])) last --;
            pl[++last] = i;
        }
        for(int i=0;i<=last;i++) clist.push_back(pl[i]);
        clist.push_back(clist[0]);
        reverse(clist.begin(), clist.end());
        return;
    }

    void half_plane_intersection() {
        for(int i=0;i<(int)clist.size()-1;i++) {
            twodpoint one = temp[clist[i]];
            twodpoint two = temp[clist[i+1]];
            double a = one.y - two.y;
            double b = two.x - one.x;
            double c= -one.y * b -one.x * a - hypot(b,-a) * eps2;
            hp.push_back({a,b,c});
        }
        sort(hp.begin(), hp.end(), [&](const halfplane &a, const halfplane &b){
            return atan2(-a.b, a.a) < atan2(-b.b, b.a);
        });
        normalize(hp);

        deque<halfplane> DQ;
        DQ.push_back(hp[0]);
        DQ.push_back(hp[1]);
        for (int i = 2; i < hp.size(); i++) {
            while(DQ.size() > 1 && out(*----DQ.end(), *--DQ.end(), hp[i])) {
                if(overpi(*----DQ.end(), hp[i])) break;
                DQ.pop_back();
            }
            while(DQ.size() > 1 && out(hp[i], *DQ.begin(), *++DQ.begin())) {
                if(overpi(*++DQ.begin(), hp[i])) break;
                DQ.pop_front();
            }
            DQ.push_back(hp[i]);
        }
        if(DQ.size() > 1 && out(*----DQ.end(), *--DQ.end(), *DQ.begin())) {
            if(overpi(*----DQ.end(), *DQ.begin()) == false) DQ.pop_back(); 
        }

        for(int i=0; i<DQ.size(); i++) {
            pi crs = cross(DQ[i], DQ[(i+1)%DQ.size()]);
            inconvex.push_back({crs.first,crs.second,0});
        }
        int cut = 0;
        int vs = inconvex.size();
        for(int i=0;i<vs;i++) inconvex.push_back(inconvex[i]);
        int left, right;
        double minx = 1e9;
        for(int i=0;i<vs;i++) {
            if(inconvex[i].x < minx) {
                minx = inconvex[i].x;
                right = i;
            }
        }
        left = right;
        minx = -1e9;
        for(int i=left;i<left+vs;i++) {
            if(inconvex[i].x > minx) {
                minx = inconvex[i].x;
                right = i;
            }
        }
        for(int i=0;i<planesize;i++) {
            twodpoint now = temp[i];
            int lo = left, hi = right;
            if(now.x > inconvex[hi].x || now.x < inconvex[lo].x) {
                // isobject[now.tag] = false;
            } else {
                while(lo < hi) {
                    int mid = (lo+hi)/2;
                    if(inconvex[mid].x < now.x) lo = mid + 1;
                    else hi = mid;
                }
                bool up1 = ccw(inconvex[hi-1], inconvex[hi], now);
                lo = right, hi = left+vs-1;
                while(lo < hi) {
                    int mid = (lo+hi)/2;
                    if(inconvex[mid].x < now.x) hi = mid;
                    else lo = mid+1;
                }
                bool up2 = ccw(inconvex[hi], inconvex[hi-1], now);
                //if(up2 ^ up1) isobject[now.tag] = true;
                if(up2 ^ up1) {
                    object[now.tag].second ++;
                }
                object[now.tag].first ++;
                //else isobject[now.tag] = false;
            }   
        }
        return;
    }
} plane;
 
void TwoDwork() {
    for(int i = 0; i < divide; i++){
        double deg = 2.0 * (double)i * PI / (double) divide;
		plane.init(deg);
		plane.error_tolerant_convex_hull();
	}
	return;
}

void plane_sweep() {
    int front = 0;
    for(int i=0;i<inputsize;i++) {
        while(front < inputsize && plist[front].z < plist[i].z - dadj) {
            seg.del(plist[front].x, plist[front].y, plist[front].z, plist[front].tag);
            front ++;
        }
        seg.add(plist[i].x, plist[i].y, plist[i].z, plist[i].tag);
    }
    while(front < inputsize) {
        seg.del(plist[front].x, plist[front].y, plist[front].z, plist[front].tag);
        front ++;
    }
    return;
}
 
void boundary() {
    queue<point> q;
    for(int i=0;i<inputsize;i++) {
        if((double)object[plist[i].tag].second / (double)object[plist[i].tag].first > 1.0) isobject[plist[i].tag] = false;
    }
    for(int i=0;i<inputsize;i++) if(isobject[i]) q.push(plist[i]);
    return;
    while(!q.empty()) {
        point t = q.front();
        int now = t.tag;
        q.pop();
        for(int i=0;i<(int)seg.adjpoint[now].size();i++) {
            int nxt = seg.adjpoint[now][i];
            if(!isobject[nxt]) {
                cntobj[nxt] ++;
                if((double) cntobj[nxt] / (double) seg.adjpoint[nxt].size() > limit) {
                    isobject[nxt] = true;
                    q.push(plist[cursor[nxt]]);
                }
            }
        }
    }
    return;
}

void init() {
	for(int i=0;i<inputsize;i++) {
		vx.push_back(plist[i].x);
		vy.push_back(plist[i].y);
	}
    sort(vx.begin(), vx.end());
    sort(vy.begin(), vy.end());
    vx.erase(unique(vx.begin(), vx.end()), vx.end());
    vy.erase(unique(vy.begin(), vy.end()), vy.end());
    seg.init((int)vx.size());
    sort(plist,plist+inputsize, [&](const point &a, const point &b){
            return a.z < b.z;
    });
    for(int i=0;i<inputsize;i++) cursor[plist[i].tag] = i;
}
 
void solve() {
	init();
    TwoDwork();
    /*
    for(dadj = 0.012501; dadj < 0.0601; dadj += 0.0025) {
    	for(limit = 0.2; limit < 0.601; limit += 0.02) {
    		for(int i=0;i<inputsize;i++) seg.adjpoint[i].clear();
    		md();
    		plane_sweep();
    		boundary();
    		int cnt = 0, realcnt = 0;
    		for(int i=0;i<inputsize;i++) {
                if(fakestr[i]) {
                    cnt ++;
                    if(isobject[i]) realcnt ++;
                }
                if(!isobject[i]) {
                    cnt ++;
                    if(i < 23979) realcnt ++;
                }
    		}
    		FILE* out = fopen("chart2 (3).txt","a");
    		fprintf(out, "%d %d %d %d\n", (int)(dadj/0.0025), (int)(limit/0.02), cnt, realcnt);
    		fclose(out);
    	}
    }
    */
    //md();
    plane_sweep();
    boundary();
    return;
}
 
void input() {
	while(scanf("%lf %lf %lf",&plist[inputsize].x, &plist[inputsize].y, &plist[inputsize].z) != -1) {
        plist[inputsize].tag = inputsize;
        inputsize ++;
    }
    return;
}
 
void output() {
    freopen("output2.txt","w",stdout);
    for(int i=0;i<inputsize;i++) {
    	//if(isobject[plist[i].tag]) continue;
        if((double) object[plist[i].tag].second / object[plist[i].tag].first > 0.8) continue;
		if(plist[i].tag > 2156) printf("%.4lf %.4lf %.4lf 255 255 255\n", plist[i].x, plist[i].y, plist[i].z);
		else printf("%.4lf %.4lf %.4lf 0 255 0\n", plist[i].x, plist[i].y, plist[i].z);
    }
    return;
}
 
int main() {
    input();
    solve();
    output();
}