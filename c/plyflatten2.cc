// take a series of ply files and produce a digital elevation map

#include <assert.h>
#include <cmath>
#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "lists.c"
#include "fail.c"
//#include "xmalloc.c"

#include <vector>
#include <algorithm>    // std::sort

#define USE_GDAL // TODO: add an alternative interface (e.g. geotiff)

#ifdef USE_GDAL
#include "gdal.h"
#include "ogr_api.h"
#include "ogr_srs_api.h"
#include "cpl_conv.h"
#include "cpl_string.h"
#endif

// TODO: remove these environment variables, use explicit options instead
#include "smapa.h"
SMART_PARAMETER(PRECISION,10)
SMART_PARAMETER_SILENT(NUMBER_OF_KMEANS_ITERATIONS,5)


struct ply_property {
	enum {UCHAR,FLOAT,DOUBLE} type;
	char name[0x100];
	size_t len;
};

static bool parse_property_line(struct ply_property *t, char *buf)
{
	char typename_[0x100];
	bool r = 2 == sscanf(buf, "property %s %s\n", typename_, t->name);
	if (!r) return r;
	else if (!strcmp(typename_, "uchar")) { t->type = ply_property::UCHAR;  t->len = 1;}
	else if (!strcmp(typename_, "float")) { t->type = ply_property::FLOAT;  t->len = 4;}
	else if (!strcmp(typename_, "double")){ t->type = ply_property::DOUBLE; t->len = 8;}
	else fail("Unknown property type: %s\n", buf);
	return r;
}



// fast forward "f" until "end_header" is found
// returns the number of 'properties'
// the array of structures *t, contains the names and sizes
// the properties in bytes, isbin is set if binary encoded
// and reads the utm zone
static size_t header_get_record_length_and_utm_zone(FILE *f_in, char *utm,
		int *isbin, struct ply_property *t)
{
	size_t n = 0;
	*isbin = 0;

	char buf[FILENAME_MAX] = {0};
	while (fgets(buf, FILENAME_MAX, f_in)) {
		if (0 == strcmp(buf, "format binary_little_endian 1.0\n"))
			*isbin=1;
		else if (0 == strcmp(buf, "format ascii 1.0\n")) *isbin=0;
		else {
			if (parse_property_line(t+n, buf))
				n += 1;
			else if (0 == strncmp(buf, "comment projection:", 19)) {
				sscanf(buf,"comment projection: UTM %3s\n",utm);
			}
		}
		if (0 == strcmp(buf, "end_header\n"))
			break;
	}
	return n;
}

static void update_min_max(double *min, double *max, double x)
{
	if (x < *min) *min = x;
	if (x > *max) *max = x;
}

// rescale a double:
// min: start of interval
// resolution: spacing between values
static int rescale_double_to_int(double x, double min, double resolution)
{
	int r = floor( (x - min) / resolution);
	return r;
}

static float recenter_double(int i, double xmin, double resolution)
{
	return xmin + resolution * (0.5 + i);
}

struct accumulator_image {
	float *min;
	float *max;
	float *cnt;
	float *avg;
	int w, h;
	std::vector<std::vector<float> > acc;
	int *counter_non_neighbors;
};




// given a set of centers, assign the index of the nearest center to each point
static void assign_each_point_to_nearest_center(int *assign, float *center,
		int k, float *x, int n)
{
	// TODO: this function should run in O(n) instead of O(n*k)
	// using the fact than the x[i] are ordered
	// and the assignement is thus monotonic
	for (int i = 0; i < n; i++)
	{
		int bj = 0;
		for (int j = 0; j < k; j++)
			if ( fabs(x[i] - center[j]) < fabs(x[i] - center[bj]) )
				bj = j;
		assign[i] = bj;
	}
}

// INPUT  x[n] : ordered array of floats
// INPUT  g[n] : array of (0..k), saying to which cluster belongs each number
// OUTPUT m[k] : ordered array of cluster centers
static void update_means_of_each_group(float *m, int *g, int k, float *x, int n)
{
	int c[k];
	for (int j = 0; j < k; j++)
		m[j] = c[j] = 0;
	for (int i = 0; i < n; i++)
	{
		m[g[i]] += x[i];
		c[g[i]] += 1;
	}
	for (int j = 0; j < k; j++)
		if (c[j])
			m[j] /= c[j];
		else
			m[j] = NAN;
}

static
void update_medians_of_each_group(float *m, int *g, int k, float *x, int n)
{
	for (int i = 0; i < n-1; i++)
		assert(x[i] <= x[i+1]);
	//fprintf(stderr, "\tupdating medians %d%d :\n", k, n);
	//fprintf(stderr, "\tx : ");
	//for (int i = 0; i < n; i++)
	//	fprintf(stderr, "%g%c", x[i], i==n-1?'\n':' ');
	//fprintf(stderr, "\tg : ");
	//for (int i = 0; i < n; i++)
	//	fprintf(stderr, "%d%c", g[i], i==n-1?'\n':' ');

	for (int j = 0; j < k; j++)
	{
		int tn = 0;
		float tx[n];
		for (int i = 0; i < n; i++)
			if (j == g[i])
				tx[tn++] = x[i];
		if (tn) {
			int a = (tn+1)/2-1;
			int b = tn/2;
			assert(a >= 0); assert(b >= 0);
			assert(a < tn); assert(b < tn);
			m[j] = (tx[a] + tx[b])/2;
			//fprintf(stderr, "\t\tnt a b m[%d] = %d %d %d %g\n",
			//		j, tn, a, b, m[j]);
		} else
			m[j] = NAN;
	}
}

static bool isgood(float *x, int n)
{
	for (int i = 0; i < n; i++)
		if (!std::isfinite(x[i]))
			return false;
	return true;
}

static int compare_floats(const void *a, const void *b)
{
	const float *da = (const float *) a;
	const float *db = (const float *) b;
	return (*da > *db) - (*da < *db);
}

// This function sorts and processes a vector x[n] for the trivial cases of 1d
// clustering algorithms.  It returns 1 if no further processing is needed.
//
// x[n] : array of floats that will be sorted
// m[k] : computed clusters or nan, in some trivial cases
// return value : whether the compoutation is already finished for this vector.
static int sort_and_sanitize_and_check(float *m, float *x, int n, int k)
{
	for (int i = 0; i < k; i++)
		m[i] = NAN;
	if (!n)
		return 1;
	qsort(x, n, sizeof*x, compare_floats);
	if (n <= k) {
		for (int i = 0; i < n; i++)
			m[i] = x[i];
		return 1;
	}
	return 0;
}

// INPUT  x[n] : ordered array of numbers
// OUTPUT m[k] : centers uniformly-distributed clusters, to be filled-in
static void initialize_clusters_uniformly(float *m, float *x, int n, int k)
{
	assert(n > k);
	for (int i = 0; i < k; i++)
	{
		int idx = lrint(  (i + 1.0) * (n - 1.0) / (k + 1.0)  );
		assert(idx >= 0);
		assert(idx < n);
		m[i] = x[idx];
	}

	// The following hack is needed for the particular case when
	// a lot of the input numbers are exactly the same number.
	//
	// It solves the case when all the clusters collapse into this point.
	float wiggle = 0.00001;
	for (int i = 1; i < k; i++)
		if (m[i-1] == m[i])
		{
			m[i-1] -= wiggle;
			m[i] += wiggle;
		}
}


// the standard k-means algorithm for 1d points
static void kmeans_1d(float *means, float *x, int n, int k)
{
	if (sort_and_sanitize_and_check(means, x, n, k))
		return;

	initialize_clusters_uniformly(means, x, n, k);

	int numit = NUMBER_OF_KMEANS_ITERATIONS();
	for (int cx = 0; cx < numit; cx++)
	{
		int group[n]; // to which cluster belongs each point
		assign_each_point_to_nearest_center(group, means, k, x, n);
		update_means_of_each_group(means, group, k, x, n);
	}
}

// the standard k-means algorithm for 1d points
static void kmedians_1d(float *means, float *x, int n, int k)
{
	if (sort_and_sanitize_and_check(means, x, n, k))
		return;

	initialize_clusters_uniformly(means, x, n, k);

	int numit = NUMBER_OF_KMEANS_ITERATIONS();
	for (int cx = 0; cx < numit; cx++)
	{
		int group[n]; // to which cluster belongs each point
		assign_each_point_to_nearest_center(group, means, k, x, n);
		update_medians_of_each_group(means, group, k, x, n);
		//update_means_of_each_group(means, group, k, x, n);
	}
}


// INPUT: n samples x[i], desired output dimension "dy"
// OUTPUT:
// y[0] = number of modes of the samples x[i] (must satisfy y[0] < dy-1)
// y[1] = position of first mode
// y[2] = position of second mode
// ...
// y[y[0]] = position of the last mode
// y[y[0]+1] = nan
// ...
// y[dy-1] = nan
static void float_kmeans(float *y, int dim_y, float *x, int n, int k)
{
	for (int i = 0; i < dim_y; i++) y[i] = NAN;
	if (k >= dim_y) k = dim_y - 1;
	float means[k];
	kmeans_1d(means, x, n, k);
	int count = 0;
	for (int i = 0; i < k; i++)
		count += std::isfinite(means[i]);
	y[0] = count;
	int ypos = 1;
	for (int i = 0; i < k; i++)
		if (std::isfinite(means[i]))
			y[ypos++] = means[i];
}


static void float_kmedians(float *y, int dim_y, float *x, int n, int k)
{
	for (int i = 0; i < dim_y; i++) y[i] = NAN;
	if (k >= dim_y) k = dim_y - 1;
	float medians[k];
	kmedians_1d(medians, x, n, k);
	int count = 0;
	for (int i = 0; i < k; i++)
		count += std::isfinite(medians[i]);
	y[0] = count;
	int ypos = 1;
	for (int i = 0; i < k; i++)
		if (std::isfinite(medians[i]))
			y[ypos++] = medians[i];
}

// compute the avg of the variances of each cluster
static float average_of_cluster_variances(
		int *group, float *mean, int k,
		float *x, int n)
{
	if (!k) return 0;
	float var[k], cnt[k];
	for (int i = 0; i < k; i++)
		var[i] = cnt[i] = 0;

	for (int i = 0; i < n; i++)
	{
		float vi = x[i];
		int gi = group[i];
		assert(gi >= 0);
		assert(gi <  k);
		var[gi] += (x[i] - mean[gi]) * (x[i] - mean[gi]);
		cnt[gi] += 1;
	}
	for (int i = 0; i < k; i++)
		var[i] /= cnt[i];

	float r = 0;
	for (int i = 0; i < k; i++)
		r += var[i];
	return r / k;
}

// compute the avg of the diq of each cluster
static float average_of_cluster_diq(
		int *group, float *mean, int k,
		float *x, int n)
{
	(void)mean;
	if (!k) return 0;
	float q25[k], q75[k];

	for (int j = 0; j < k; j++)
	{
		int tn = 0;
		float tx[n];
		for (int i = 0; i < n; i++)
			if (j == group[i])
				tx[tn++] = x[i];
		assert(tn);
		int a[2] = {(tn+1)/4-1, tn/4 };
		int b[2] = {(3*tn+1)/4-1, (3*tn)/4 };
		//fprintf(stderr, "\tq25(%d) = %d %d\tq75(%d) = %d %d\n",
		//		tn, a[0], a[1], tn, b[0], b[1]);
		for (int i = 0; i < 2; i++) {
			if (a[0] < 0) a[0] = 1;
			if (a[1] < 0) a[1] = 1;
			if (b[0] < 0) b[0] = 1;
			if (b[1] < 0) b[1] = 1;
			if (a[0] >= tn) a[0] = tn-1;
			if (a[1] >= tn) a[1] = tn-1;
			if (b[0] >= tn) b[0] = tn-1;
			if (b[1] >= tn) b[1] = tn-1;
			assert(a[i] >= 0); assert(b[i] >= 0);
			assert(a[i] < tn); assert(b[i] < tn);
		}
		// TODO: use the corrected coefficients of 1/3 & 2/3 here:
		q25[j] = (tx[a[0]] + tx[a[1]])/2;
		q75[j] = (tx[b[0]] + tx[b[1]])/2;
	}

	float r = 0;
	for (int i = 0; i < k; i++)
		r += q75[i] - q25[i];
	return r / k;
}

// run k-means with increasing k until the average variance of the clusters
// falls below a pre-sed precision
static void float_xmeans(float *y, int dim_y, float *x, int n, float prec)
{
	for (int pre_k = 1; pre_k < dim_y; pre_k++)
	{
		float_kmeans(y, dim_y, x, n, pre_k);
		int k = y[0];
		int group[n];
		assign_each_point_to_nearest_center(group, y+1, k, x, n);
		float acv = average_of_cluster_variances(group, y+1, k, x, n);
		if (acv < prec*prec)
			break;
	}
}


// run k-means with increasing k until the average variance of the clusters
// falls below a pre-sed precision
static void float_xmedians(float *y, int dim_y, float *x, int n, float prec)
{
	for (int pre_k = 1; pre_k < dim_y; pre_k++)
	{
		//fprintf(stderr,"xmedians of n = %d with pre_k = %d\n",n,pre_k);
		float_kmedians(y, dim_y, x, n, pre_k);
		int k = y[0];
		int group[n];
		assign_each_point_to_nearest_center(group, y+1, k, x, n);
		float acv = average_of_cluster_diq(group, y+1, k, x, n);
		//float acv = average_of_cluster_variances(group, y+1, k, x, n);
		//fprintf(stderr, "...got k=%d acv=%g\n", k, acv);
		//for (int i = 0; i < n; i++)
		//	fprintf(stderr, "...x[%d] = %g\n", i, x[i]);
		//for (int i = 0; i < n; i++)
		//	fprintf(stderr, "...group[%d] = %d\n", i, group[i]);
		//for (int i = 0; i < 1+k; i++)
		//	fprintf(stderr, "...y[%d] = %g\n", i, y[i]);
		if (acv < prec)
			break;
	}
}















// update the output images with a new height
static void accumulate_height(
		struct accumulator_image *x,
		int i, int j,         // position of the new height
		double v,             // new height
		float weight,         // relative weight
		bool updateminmax     // whether to update min,max fields
		                      // (only makes sense when radius=1)
		)
{
	uint64_t k = (uint64_t) x->w * j + i;
	if (updateminmax) {
		x->min[k] = fmin(x->min[k], v);
		x->max[k] = fmax(x->max[k], v);
	}
	x->avg[k] = (v * weight + x->cnt[k] * x->avg[k]) / (weight + x->cnt[k]);
	x->cnt[k] += weight;
	x->acc[k].push_back(v);
}

size_t get_record(FILE *f_in, int isbin, struct ply_property *t, int n, double *data){
	size_t rec = 0;
	if(isbin) {
		for (int i = 0; i < n; i++) {
			switch(t[i].type) {
        case ply_property::UCHAR: {
				unsigned char X;
				size_t r = fread(&X, 1, 1, f_in);
				if (r != 1)
					return rec;
				rec += r;
				data[i] = X;
				break; }
        case ply_property::FLOAT: {
				float X;
				size_t r = fread(&X, sizeof(float), 1, f_in);
				if (r != 1)
					return rec;
				rec += r;
				data[i] = X;
				break; }
        case ply_property::DOUBLE: {
				 double X;
				 size_t r = fread(&X, sizeof(double), 1, f_in);
				 if (r != 1)
					 return rec;
				 rec += r;
				 data[i] = X;
				 break; }
			}
		}
	} else {
		int i=0;
		while (i < n && !feof(f_in)) {
			rec += fscanf(f_in,"%lf", &data[i]);  i++;
		}
	}
	return rec;
}

// open a ply file, read utm zone in the header, and update the known extrema
static void parse_ply_points_for_extrema(double *xmin, double *xmax,
		double *ymin, double *ymax,
		char *utm, char *fname)
{
	FILE *f = fopen(fname, "r");
	if (!f) {
		fprintf(stderr, "WARNING: can not open file \"%s\"\n", fname);
		return;
	}

	int isbin=0;
	struct ply_property t[100];
	size_t n = header_get_record_length_and_utm_zone(f, utm, &isbin, t);
	//fprintf(stderr, "%d\n", n);
	//fprintf(stderr, "%s\n", utm);

	double data[n];
	while ( n == get_record(f, isbin, t, n, data) ) {
		update_min_max(xmin, xmax, data[0]);
		update_min_max(ymin, ymax, data[1]);
	}
	fclose(f);
}

// check whether a point is inside the image domain
static int insideP(int w, int h, int i, int j)
{
	return i>=0 && j>=0 && i<w && j<h;
}

static float distance_weight(float sigma, float d)
{
	if (isinf(sigma))
		return 1;
	else
		return exp(-d*d/(2*sigma*sigma));
}

// open a ply file, and accumulate its points to the grand image
static void accumulate_ply_points_to_images(
		struct accumulator_image *x,
		double xmin,  double ymax,  // origin of output grid
		double R,                   // resolution of output grid
		char utm_zone[3],
		char *fname,
		int col_idx,
		int radius,
		double sigma)
{
	FILE *f = fopen(fname, "r");
	if (!f) {
		fprintf(stderr, "WARNING: can not open file \"%s\"\n", fname);
		return;
	}

	// check that the utm zone is the same as the provided one
	char utm[5];
	int isbin=1;
	struct ply_property t[100];
	size_t n = header_get_record_length_and_utm_zone(f, utm, &isbin, t);
	if (0 != strncmp(utm_zone, utm, 3))
		fprintf(stderr, "error: different UTM zones among ply files\n");

	if (col_idx < 2 || col_idx > 5)
		exit(fprintf(stderr, "error: bad col_idx %d\n", col_idx));

	double data[n];
	double sigma2mult2 = 2*sigma*sigma;
	bool updatemmx = radius == 0;

	while ( n == get_record(f, isbin, t, n, data) )
	{
		int i = rescale_double_to_int(data[0], xmin, R);
		int j = rescale_double_to_int(-data[1], -ymax, R);
                
		if (insideP(x->w, x->h, i, j)) {
			x->counter_non_neighbors[x->w * j + i] ++;
		}

		for (int k1 = -radius; k1 <= radius; k1++)
		for (int k2 = -radius; k2 <= radius; k2++) {
			int ii = i + k1;
			int jj = j + k2;
			float dist_x = data[0] - recenter_double(ii, xmin, R);
			float dist_y = data[1] - recenter_double(jj, ymax, -R);
			float dist = hypot(dist_x, dist_y);
			float weight = distance_weight(sigma, dist);

			if (insideP(x->w, x->h, ii, jj)) {
				if (col_idx == 2) {
					accumulate_height(x, ii, jj,
						data[2], weight, updatemmx);
					assert(std::isfinite(data[2]));
				}
				else {
					unsigned int rgb = data[col_idx];
					accumulate_height(x, ii, jj,
						rgb, weight, updatemmx);
				}
			}
		}
	}
	fclose(f);
}

static void save_output_image_with_utm_georeferencing(
		char *filename,
		float *x, int w, int h,                    // data to save
		double g_xoff, double g_xdx, double g_xdy, // geo-transform
		double g_yoff, double g_ydx, double g_ydy,
		char *utm                                  // utm zone string
		)
{
#ifdef USE_GDAL
	GDALAllRegister();
	char **papszOptions = NULL;
	const char *pszFormat = "GTiff";
	GDALDriverH hDriver = GDALGetDriverByName( pszFormat );
	GDALDatasetH hDstDS = GDALCreate( hDriver, filename,
					  w, h, 1, GDT_Float32,
					  papszOptions );

	double adfGeoTransform[6] = {g_xoff,g_xdx,g_xdy, g_yoff,g_ydx,g_ydy};
	OGRSpatialReferenceH hSRS;
	char *pszSRS_WKT = NULL;
	GDALRasterBandH hBand;
	GDALSetGeoTransform( hDstDS, adfGeoTransform );
	hSRS = OSRNewSpatialReference( NULL );
	char utmNumber[3];
	utmNumber[0] = utm[0];
	utmNumber[1] = utm[1];
	utmNumber[2] = '\0';
	int nZone = atoi(utmNumber);
	int bNorth = (utm[2] == 'N');
	OSRSetUTM( hSRS, nZone, bNorth );
	OSRSetWellKnownGeogCS( hSRS, "WGS84" );
	OSRExportToWkt( hSRS, &pszSRS_WKT );
	OSRDestroySpatialReference( hSRS );
	GDALSetProjection( hDstDS, pszSRS_WKT );
	CPLFree( pszSRS_WKT );
	hBand = GDALGetRasterBand( hDstDS, 1 );
	int r = GDALRasterIO( hBand, GF_Write, 0, 0, w, h,
			  x, w, h, GDT_Float32,
			  0, 0 );
	if (r != 0)
		fprintf(stderr, "ERROR: cannot write %s\n", filename);
	GDALClose( hDstDS );
#endif//USE_GDAL
}


void help(char *s)
{
	fprintf(stderr, "usage:\n\t"
			"ls files | %s [-c column] "
			"[-srcwin \"xoff yoff xsize ysize\"] "
			"[-radius 0] [-sigma resolution] "
			"resolution out.tif\n", s);
	fprintf(stderr, "\t the resolution is in meters per pixel\n");
}

#include "pickopt.c"

int main(int c, char *v[])
{
	int col_idx = atoi(pick_option(&c, &v, (char*)"c", (char*)"2"));
	char *srcwin = pick_option(&c, &v, (char*)"srcwin", (char*)"");
	int radius = atoi(pick_option(&c, &v, (char*)"radius", (char*)"0"));
	float sigma = atof(pick_option(&c, &v, (char*)"sigma", (char*)"inf"));

	// process input arguments
	if (c != 3) {
		help(*v);
		return 1;
	}

	double resolution = atof(v[1]);
	char *filename_out = v[2];

	// initialize x, y extrema values
	double xmin = INFINITY;
	double xmax = -INFINITY;
	double ymin = INFINITY;
	double ymax = -INFINITY;

	// Subwindow from the source
	double xoff, yoff;
	int xsize, ysize;

	// process each filename from stdin to determine x, y extrema and store
	// the filenames in a list of strings, to be able to open the files
	// again
	char fname[FILENAME_MAX], utm[5];
	struct list *l = NULL;
	while (fgets(fname, FILENAME_MAX, stdin))
	{
		strtok(fname, "\n");
		l = push(l, fname);
		parse_ply_points_for_extrema(&xmin, &xmax, &ymin, &ymax,
				utm, fname);
	}

	if (0 != strcmp(srcwin, "") ) {
		sscanf(srcwin, "%lf %lf %d %d", &xoff, &yoff, &xsize, &ysize);
	}
	else {
		xsize = 1 + floor((xmax - xmin) / resolution);
		ysize = 1 + floor((ymax - ymin) / resolution);
		xoff = (xmax + xmin - resolution * xsize) / 2;
		yoff = (ymax + ymin + resolution * ysize) / 2;
	}
	fprintf(stderr, "xmin: %lf, xmax: %lf, ymin: %lf, ymax: %lf\n", xmin, xmax, ymin, ymax);
	fprintf(stderr, "xoff: %lf, yoff: %lf, xsize: %d, ysize: %d\n", xoff, yoff, xsize, ysize);

	// allocate and initialize accumulator
	struct accumulator_image x[1];
	x->w = xsize;
	x->h = ysize;
	x->min = (float*) malloc(xsize*ysize*sizeof(float));
	x->max = (float*) malloc(xsize*ysize*sizeof(float));
	x->cnt = (float*) malloc(xsize*ysize*sizeof(float));
	x->avg = (float*) malloc(xsize*ysize*sizeof(float));
	x->counter_non_neighbors = (int*) malloc(xsize*ysize*sizeof(int));
	for (uint64_t i = 0; i < (uint64_t) xsize*ysize; i++)
	{
		x->min[i] = INFINITY;
		x->max[i] = -INFINITY;
		x->cnt[i] = 0;
		x->avg[i] = 0;
	}
	x->acc = std::vector<std::vector<float>  >(xsize*ysize);

	// process each filename to accumulate points in the dem
	while (l != NULL)
	{
		// printf("FILENAME: \"%s\"\n", l->current);
		accumulate_ply_points_to_images(x, xoff, yoff, resolution, utm,
				l->current, col_idx, radius, sigma);
		l = l->next;
	}

	// set unknown values to NAN
	for (uint64_t i = 0; i < (uint64_t) xsize*ysize; i++)
		if (!x->cnt[i])
			x->avg[i] = NAN;

	// use k-medians instead of average
	if (1)
	for (uint64_t i = 0; i < (uint64_t) xsize*ysize; i++) {
		int n = x->acc[i].size();
		//x->avg[i] = n; continue;
		if (n<3) { x->avg[i] = std::isfinite(x->max[i]) ? x->max[i]: NAN; continue;}

		int out_pd = 3;
		float tmp[100000];
		float y[out_pd];
		int ngood = 0;
		for (int j = 0; j < n; j++)
			//if (isgood(x[j]+i, 1)) 
			{
				tmp[ngood] = x->acc[i][j];
				ngood += 1;
			}

		float_xmedians(y, out_pd, tmp, ngood, PRECISION());

		// allow up to 3 clusters. 
		// if 3 -> NAN
		// if 1 -> average
		// if 2 -> upper cluster
		if (y[0] < 3 && x->counter_non_neighbors[i] > 0) {
			x->avg[i] = y[0] == 2 ? y[2] : y[1];
		} else {
			x->avg[i] = NAN;
		}
	}
	

	// save output image
	save_output_image_with_utm_georeferencing(
			filename_out,
			x->avg, x->w, x->h,
			xoff, resolution, 0, yoff, 0, -resolution, utm
			);

	// cleanup and exit
	free(x->min);
	free(x->max);
	free(x->cnt);
	free(x->avg);
	return 0;
}
