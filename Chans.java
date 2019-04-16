import java.awt.geom.*;
import java.awt.Point;
import java.util.*;
import java.io.*;

/**
 * A direct port to Java of the "Chans Algorithm" C++ implementation from
 * https://github.com/ypranay/Convex-Hull
 */
public class Chans {
    private static final int RIGHT_TURN = -1;
    private static final int LEFT_TURN = 1;
    private static final int COLINEAR = 0;
    // Note: the java.awt.Point class is used to store a pair of ints. They're not geometric points.

    /**
     * Returns the index of the point to which the tangent is drawn from point p.
     * Uses a modified Binary Search Algorithm to yield tangent in O(log n) complexity
     * @param v List of Points representing the hull, aka the vector of hull points
     * @param p Point from where tangent needs to be drawn
     * @return the index of the point to which the tangent is drawn from point p
     */
    private static int tangent(List<Point2D> v, Point2D p) {
        int l = 0;
        int r = v.size();
        int l_before = orientation(p, v.get(0), v.get(v.size()-1));
        int l_after = orientation(p, v.get(0), v.get((l + 1) % v.size()));
        while (l < r) {
            int c = (l + r) >> 1;
            int c_before = orientation(p, v.get(c), v.get((c + r - 1) % v.size()));
            int c_after = orientation(p, v.get(c), v.get((c + 1) % v.size()));
            int c_side = orientation(p, v.get(l), v.get(c));
            if (c_before != RIGHT_TURN && c_after != RIGHT_TURN) {
                return c;
            } else if ((c_side == LEFT_TURN && (l_after == RIGHT_TURN || l_before == l_after)) || (c_side == RIGHT_TURN && c_before == RIGHT_TURN)) {
                r = c;
            } else {
                l = c + 1 ;
            }
            l_before = -c_after; 
            if (l < v.size()) { // Note this test not in original C++ source, which overflows
                l_after = orientation(p, v.get(l), v.get((l + 1) % v.size()));
            }
        }
        return l;
    }

    /**
     * Returns the pair of integers representing the Hull # and the point in that Hull which is the
     * extreme amongst all given Hull Points
     * @param hulls: Vector containing the hull points for various hulls stored as individual vectors.
     */
    private static Point extreme_hullpt_pair(List<List<Point2D>> hulls) {
        int h=0, p=0;
        for (int i=0;i<hulls.size();++i) {
            int min_index=0;
            double min_y = hulls.get(i).get(0).getY();
            for (int j=1;j<hulls.get(i).size();++j) {
                if (hulls.get(i).get(j).getY() < min_y){
                    min_y = hulls.get(i).get(j).getY();
                    min_index = j;
                }
            }
            if (hulls.get(i).get(min_index).getY() < hulls.get(h).get(p).getY()) {
                h = i;
                p = min_index;
            }
        }
        return new Point(h, p);
    }

    /**
     * Returns the pair of integers representing the Hull # and the point in that Hull to which the point lpoint will be joined
     * @param hulls: Vector containing the hull points for various hulls stored as individual vectors.
     * @param lpoint: Pair of the Hull # and the leftmost extreme point contained in that hull, amongst all the obtained hulls
     */
    private static Point next_hullpt_pair(List<List<Point2D>> hulls, Point lpoint) {
        Point2D p = hulls.get(lpoint.x).get(lpoint.y);
        Point next = new Point(lpoint.x, (lpoint.y + 1) % hulls.get(lpoint.x).size());
        for (int h=0;h<hulls.size();h++) {
            if (h != lpoint.x) {
                int s = tangent(hulls.get(h), p);
                Point2D q = hulls.get(next.x).get(next.y);
                if (s < hulls.get(h).size()) { // Note this test not in original C++ source, which overflows
                    Point2D r = hulls.get(h).get(s);
                    int t = orientation(p, q, r);
                    if (t == RIGHT_TURN || (t == COLINEAR && p.distance(r) > p.distance(q))) {
                        next = new Point(h, s);
                    }
                }
            }
        }
        return next;
    }

    /**
     * Returns orientation of the line joining points p and q and line joining points q and r
     * @param p first point
     * @param q second point
     * @param r third point
     * @return -1: CW orientation, +1: CCW orientation, 0: Collinear
     */
    private static int orientation(Point2D p, Point2D q, Point2D r) {
	double val = (q.getY() - p.getY()) * (r.getX() - q.getX()) - (q.getX() - p.getX()) * (r.getY() - q.getY());
        return val == 0 ? 0 : val > 0 ? -1 : 1; // Colinear=0, CW=-1 CCW=1
    }

    /**
     * Constraint to find the outermost boundary of the points by checking if the points lie to the left otherwise adding the given point p
     * @param v List of all the points
     * @param p New point p which will be checked to be in the Hull Points or not
     * @return the Hull Points
     */
    private static void keep_left(List<Point2D> v, Point2D p) {
        while (v.size() > 1 && orientation(v.get(v.size()-2), v.get(v.size()-1), p) != LEFT_TURN) {
            v.remove(v.size() - 1);
        }
	if (v.isEmpty() || !v.get(v.size() - 1).equals(p)) {
            v.add(p);
        }
    }

    /**
     * Graham Scan algorithm to find convex hull from the given set of points
     * @param points List of the given points in the cluster (as obtained by Chan's Algorithm grouping)
     * @return the Hull Points in a vector
     */
    private static List<Point2D> grahamScan(List<Point2D> points) {
        if (points.size() <= 1) {
            return points;
        }
        Collections.sort(points, new Comparator<Point2D>() {
            final Point2D p0 = new Point2D.Double();
            public int compare(Point2D p1, Point2D p2) {
                int orient = orientation(p0, p1, p2);
                if (orient == 0) {
                    return p0.distance(p2) >= p0.distance(p1) ? -1 : 1;
                }
                return orient == 1 ? -1: 1;
            }
        });
        List<Point2D> lower_hull = new ArrayList<Point2D>();
        for(int i=0;i<points.size();++i) {
            keep_left(lower_hull, points.get(i));
        }
        Collections.reverse(points);
        List<Point2D> upper_hull = new ArrayList<Point2D>();
        for(int i=0;i<points.size();++i) {
            keep_left(upper_hull, points.get(i));
        }
        for(int j=1;j<upper_hull.size();++j) {
            lower_hull.add(upper_hull.get(j));
        }
        return lower_hull;   
    }

    /**
     * Implementation of Chan's Algorithm to compute Convex Hull in O(nlogh) complexity
     * @param v the List of input Points
     * @return a List of Points that form the Convex Hull of the input
     */
    public static List<Point2D> chansalgorithm(List<Point2D> v) {
        for(int t=0;t<v.size();++t) {
            for (int m=1;m<(1<<(1<<t));++m) {
                List<List<Point2D>> hulls = new ArrayList<List<Point2D>>();
                for (int i=0;i<v.size();i=i+m) {
                    List<Point2D> chunk = new ArrayList<Point2D>();
                    if (i + m <= v.size()) {
                        chunk.addAll(v.subList(i, i + m));
                    } else {
                        chunk.addAll(v.subList(i, v.size()));
                    }
                    hulls.add(grahamScan(chunk));
		}
                System.out.println("\nM (Chunk Size): "+m);
                for (int i=0;i<hulls.size();++i) {
                    System.out.println("Convex Hull for Hull #"+i+" (Obtained using Graham Scan!!)");
                    for(int j=0; j<hulls.get(i).size();++j) {
                        System.out.print(hulls.get(i).get(j)+" ");
                    }
                    System.out.println();
                }
                List<Point> hull = new ArrayList<Point>();
                hull.add(extreme_hullpt_pair(hulls));
                for (int i=0;i<m;++i) {
                    Point p = next_hullpt_pair(hulls, hull.get(hull.size()-1));
                    List<Point2D> output = new ArrayList<Point2D>();
                    if (p.equals(hull.get(0))) {
                        for (int j=0;j<hull.size();++j){
                            output.add(hulls.get(hull.get(j).x).get(hull.get(j).y));
                        }
                        return output;
                    }
                    hull.add(p);
                }
            }
        }
        return null;
    }

    public static void main(String[] args) throws Exception {
        String s;
        BufferedReader r = new BufferedReader(new InputStreamReader(System.in));
        int num = Integer.parseInt(r.readLine());
        List<Point2D> l = new ArrayList<Point2D>();
        for (int i=0;i<num;i++) {
            String[] t = s.split(" ");
            l.add(new Point2D.Double(Double.parseDouble(t[0]), Double.parseDouble(t[1])){
                public String toString() {
                    // To give the same output as the C++ original
                    return "("+((int)Math.round(getX()))+","+((int)Math.round(getY()))+")";
                }
            });
        }
        List<Point2D> output = chansalgorithm(l);
        System.out.println("\n---------After Using Chan's Algorithm---------------");
        System.out.println("\n***************** CONVEX HULL **********************");
        for (int i=0;i<output.size();++i) {
            System.out.print(output.get(i) + " ");
        }
        System.out.println();
    }
}
