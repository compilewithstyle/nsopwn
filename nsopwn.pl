#!/usr/bin/env perl 

#--------------------------------------------------------------------------------
#  [Author]:
#  	Written by Nicholas Siow | n.siow@wustl.edu
#  
#  [Description]:
#  	Parses fastnmap output and builds a CSV file for excel from
#	that information
#  
#  [Revision History]:
#  	2014-12-11	broke script into subroutines, added &device_type_try
#  			that will look at various fields to try to determine
#  			OS info / identity of the device
#  	2014-06-30	finished script, tested and seems to be working.
#  	2014-06-27	switched to perl from python, better nmap-parsing lib
#	2015-12-04	overhaul of new rules from Brian's manual work
#  
#  [Todo]:
#	+ add import for subnet data
#--------------------------------------------------------------------------------

use strict;
use warnings;

use DBI;
use JSON;
use File::Slurp;
use Tie::IxHash;
use Data::Dumper;
use Nmap::Parser;
use Getopt::Std;
use Term::ANSIColor;
use Hash::Flatten qw| flatten |;
use feature 'say';

# turn on STDOUT autoflush
$| = 1;

# define help string
my $HELP = <<'HELP';
nsopwn.pl: Smart fastnmap parsing for the WUSTL NSO

Usage: nsopwn.pl [OPTIONS] NMAP_RESULTS_DIR

Options:
	-s [SUBNET_FILE]
		read from the given subnet
		file to enrich the results with subnet
		info - see README for formatting details
	-q
		write to sqlite database instead of CSV
		[NOT YET IMPLEMENTED]
	-d
		turn on program debugging
	-t
		testing mode, only runs on a subset
		of the samples
HELP

# check if the user is asking for help
print $HELP and exit if grep /-h|--help/, @ARGV;
	
# parse command line arguments
our ($opt_s, $opt_q, $opt_d, $opt_t);
getopts('s:qdt');

# make sure they specified a fastnmap results directory
if( scalar @ARGV == 0 ) {
	print $HELP and exit;
}

# get the directory for fastnmap results
my $results_dir = shift @ARGV;
unless( -e $results_dir ) {
	say "[ERROR] Invalid results directory: " . $results_dir;
}

#--------------------------------------------------------------------------------
#	helper function to print progress text
#--------------------------------------------------------------------------------

my $lastblocks = 0;

my %progress_hash;
sub progress( $$ )
{
	my $done  = shift;
	my $total = shift;
	my $percentage = $done / $total;
	my $blocks = int( 50 * $percentage );

	if($blocks != $lastblocks && $blocks > 0) {
		$lastblocks = $blocks;
		printf "\r\t%s%-62s%s", colored(["white on_white"], " "),
			colored(["red on_red"], "#"x$blocks), colored(["white on_white"], " ");
	}
}

# helper function to make sure the current line is cleaned up
# before going on to the next progress text
sub progress_done( $ ) {
	my $message = shift;
	my $lastblocks = 0;
	printf "\r\t%s%-62s%s\n\t%s\n\n", colored(["white on_white"], " "),
 		colored(["green on_green"], "#"x50),
		colored(["white on_white"], " "), $message;
}

# set the current stage of the script
sub progress_set_stage( $ ) {
	say $_[0] . "...";
}

#--------------------------------------------------------------------------------
#	functions to help searching for known terms within a fastnmap result
#--------------------------------------------------------------------------------

my $known_products = <<'END';

	windows    =  windows
	microsoft  =  windows
	linux      =  linux
	ubuntu     =  linux
	fedora     =  linux
	centos     =  linux
	unix       =  linux
	red hat    =  linux
	apple	   =  apple
	solaris    =  solaris
	printer    =  printer
	laserjet   =  printer
	switch     =  switch
	camera     =  camera
	vxworks    =  vxworks
	firewall   =  firewall

END

# process known product
my @product_keys;
my @product_values;
foreach( split("\n", $known_products) ) {
        next unless $_;
        s/^\s+//;

        my @values = split(/\s+=\s+/, $_);
        push @product_keys, @values[0];
        push @product_values, @values[1];
}

# helper function to offer a hash-like interface to the
# known_products info
sub product_helper( $ ) {
	my $text = shift;

	return "" unless defined $text;

	foreach my $i (0..$#product_keys) {
		my $search = $product_keys[$i];
		return $product_values[$i]
			if $text =~ /$search/i;
	}

	return "";
}

# takes an Operating Systems string and attempts to standardize it
# by looking at the list of known products. for example, if the
# operating system contains the string 'laserjet' it will be 
# marked as a printer
sub product_search( $ )
{
	my $text = shift;
	return product_helper($text);
}

# converts the given hash object into a string and performs
# a fulltext search using the keys of the known_products array
sub fulltext_product_search( $ ) {
	my $obj = shift;
	return product_helper(Dumper($obj));
}

# takes a hash reference for a host or sub-field of the host and
# performs a full-text search across all fields of the hash looking
# for the given string
sub fulltext_term_search( $$ )
{
	my $hashobject = shift;
	my $searchterm = shift;

	my $s = index Dumper($hashobject), $searchterm;
	return $s == -1 ? 0 : 1;
}

sub extract_service( $$ ) {
	my $host = shift;
	my $port = shift;

	my ($service) = grep { $_->{port} eq $port } @{$host->{services}};
	return $service;
}

#--------------------------------------------------------------------------------
#	function to go through various fields of the host info and try
#	to determine
#--------------------------------------------------------------------------------

sub device_type_try( $ )
{
	# pull out the hash reference
	my $host = shift;

	#------------------------------------------------------------------------
	#	Attempt #1 -- use 100% confidence OS data if it exists
	#------------------------------------------------------------------------

	if( $host->{os_guess} )
	{
		# only do this for os_guesses that don't have the word " or " in
		# them, or for apple products where the " or " tends to
		# still be a high-fidelity guess
		if($host->{os_guess} =~ /apple/i || $host->{os_guess} !~ / or /i) {
			$host->{device_type} = product_search( $host->{os_guess} );
			$host->{os_flavor} = lc $host->{os_guess};
			$host->{method} = 1;
			return if $host->{device_type} ne '';
		}
	}

	#------------------------------------------------------------------------
	#	Attempt #2 -- use SMB data if that exists
	#------------------------------------------------------------------------

	if( defined $host->{smb}->{os} )
	{
		$host->{device_type} = product_search( $host->{smb}->{os} );
		$host->{os_flavor}   = lc $host->{smb}->{os};
		$host->{method} = 2;
		return if $host->{device_type} ne '';
	}

	#------------------------------------------------------------------------
	#	Attempt #3 -- use port 80/443 webserver identification
	#------------------------------------------------------------------------

	my $service;
	if( ($service = extract_service($host, 80)) || ($service = extract_service($host, 443)) )
	{
		$host->{device_type} = fulltext_product_search( $service );
		if( $service->{extrainfo} ne '' ) {
			$host->{os_flavor} = $service->{extrainfo};
		}
		elsif( $service->{product} ne '' ) {
			$host->{os_flavor} = $service->{product};
		}
		$host->{method} = 3;
		return if $host->{device_type} ne '';
	}

	#------------------------------------------------------------------------
	#	Attempt #4 -- use port 22 ssh identification
	#------------------------------------------------------------------------

	if( $service = extract_service($host, 22) )
	{
		$host->{device_type} = fulltext_product_search( $service );
		if( $service->{extrainfo} ne '' ) {
			$host->{os_flavor} = $service->{extrainfo};
		}
		elsif( $service->{product} ne '' ) {
			$host->{os_flavor} = $service->{product};
		}
		$host->{method} = 4;
		return if $host->{device_type} ne '';
	}

	#------------------------------------------------------------------------
	#	Attempt #5 -- use microsoft product info
	#------------------------------------------------------------------------

	foreach my $service ( @{$host->{services}} )
	{
		if( exists $service->{product} && product_search($service->{product}) eq 'windows' )
		{
			$host->{device_type} = 'windows';
			$host->{os_flavor}   = 'windows';
			$host->{method} = 5;
			return if $host->{device_type} ne '';
		}
	}

	#------------------------------------------------------------------------
	#	Attempt #6 -- use partial SMB data
	#------------------------------------------------------------------------

	if( exists $host->{smb}->{output} && $host->{smb}->{output} =~ /ERROR/ )
	{
			$host->{device_type} = 'windows';
			$host->{os_flavor}   = 'windows';
			$host->{method} = 6;
			return if $host->{device_type} ne '';
	}

	#------------------------------------------------------------------------
	#	Attempt #7 -- look in the hostname string for the words
	#		'mac' or 'imac'
	#------------------------------------------------------------------------

	if( exists $host->{host} )
	{
		my $hostname = $host->{host};

		if( $hostname =~ /imac/ || $hostname =~ /mac(?:\d|\.)/ )
		{
			$host->{device_type} = 'apple';
			$host->{os_flavor}   = 'osx';
			$host->{method} = 7;
			return if $host->{device_type} ne '';
		}
	}

	#------------------------------------------------------------------------
	#	Attempt #8 -- look for keywords suggesting that the host
	#		is a printer
	#------------------------------------------------------------------------

	foreach my $service ( @{$host->{services}} )
	{
		my $namestring;
		if( $service->{name} =~ /printer/i )
		{
			$host->{device_type} = 'printer';
			$namestring = $service->{name};
		}

		if( $service->{product} =~ /printer/i || $service->{name} =~ /printer/i || $service->{extrainfo} =~ /printer/i )
		{
			$host->{device_type} = 'printer';
			$namestring = $service->{product};
		}

		if( $service->{extrainfo} =~ /printer/i )
		{
			$host->{device_type} = 'printer';
			$namestring = $service->{extrainfo};
		}

		next unless defined $namestring;

		my $os_flavor = "";
		my @words = split ' ', $namestring;
		foreach( @words )
		{
			$os_flavor .= " $_" if /^[A-Z0-9]/;
		}	

		if( defined $namestring )
		{
			$host->{method} = 8;
			return if $host->{device_type} ne '';
		}
	}

	#------------------------------------------------------------------------
	#	Attempt #9 -- look for keywords in services suggesting
	#		known apple projects
	#------------------------------------------------------------------------

	foreach my $service ( @{$host->{services}} )
	{
		if( Dumper($service) =~ /apple|osx/i )
		{
			$host->{device_type} = 'apple';
			$host->{os_flavor} = '';
			$host->{method} = 9;
			return if $host->{device_type} ne '';
		}
	}

	#------------------------------------------------------------------------
	#	Attempt #10 -- look for keywords in services suggesting
	#		known cisco projects
	#------------------------------------------------------------------------

	foreach my $service ( @{$host->{services}} )
	{
		if( Dumper($service) =~ /cisco ssh/i )
		{
			$host->{device_type} = 'cisco';
			$host->{os_flavor} = '';
			$host->{method} = 10;
			return if $host->{device_type} ne '';
		}
	}


	$host->{device_type} = undef;
	$host->{os_flavor}   = undef;
	$host->{method} = -1;
}

#--------------------------------------------------------------------------------
#	function to recursively find all XML files in the given base directory
#--------------------------------------------------------------------------------

sub find_xml_files()
{
	progress_set_stage("Looking for XML files");
	my @xml_files;

	chomp ( my @files = `find $results_dir -name *xml` );
	foreach( @files ) {
		push @xml_files, $_;
		progress(scalar @xml_files, scalar @files);
	}
	progress_done(sprintf("Found %d files in directory %s", scalar @files, $results_dir));

	return \@xml_files;
}

#--------------------------------------------------------------------------------
#	function to determine which files correspond to FINISHED nmap scans
#	and read those files into memory
#--------------------------------------------------------------------------------

sub read_xml_files( $ )
{
	# pull out the list of XML files and cast to list
	my @files = @{ $_[0] };

	# iterate through files, reading in each one and adding it to
	# the list of finished scans if the completion string is found
	progress_set_stage("Reading in XML files");
	my @finished_scans;
	foreach( @files )
	{
		my @lines = read_file($_);
		push @finished_scans, $_ if grep /\/nmaprun/, @lines;
		progress( scalar @finished_scans, scalar @files );
		last if $opt_t && scalar(@finished_scans) >= 100;
	}

	progress_done(sprintf("Found %d completed scans", scalar @finished_scans));
	
	die "Found no finished nmap scans in dir: $results_dir" if scalar @finished_scans == 0;

	return \@finished_scans;
}

#--------------------------------------------------------------------------------
#	function to parse files and push host objects into an array
#--------------------------------------------------------------------------------

sub find_hosts( $ )
{
	# pull out the list of finished scans and cast to list
	my @finished_scans = @{ $_[0] };

	# initialize variables
	my $np = Nmap::Parser->new;

	# iterate through the file texts and use the Nmap::Parser
	# module to parse the data
	progress_set_stage("Parsing NMAP results");
	my @hosts;
	foreach my $file ( @finished_scans )
	{
		$np->parsefile($file);
	
		# only pull in hosts that were up
		push @hosts, $_ foreach ($np->all_hosts('up'));
		progress( scalar @hosts, scalar @finished_scans );
		last if $opt_t && scalar(@hosts) >= 100;
	}

	progress_done(sprintf("Found %d hosts", scalar @hosts));
	
	die "Nmap::Parser returned 0 hosts." if scalar @hosts == 0;

	return \@hosts;
}

#--------------------------------------------------------------------------------
#	pull info from Nmap::Parser::Host to generate the sql row data
#--------------------------------------------------------------------------------

sub parse_hosts( $ )
{
	# pull out the list of hists and cast to list
	my @hosts = @{ $_[0] };

	my @host_info;
	progress_set_stage("Attempting to determine device type / os flavor");
	foreach my $host ( @hosts )
	{
		# sql-entry hash
		my %h;
	
		#------------------------------------------------------------------------
		#	add ip and hostname info to the hash
		#------------------------------------------------------------------------
	
		$h{ip} = $host->ipv4_addr();
		$h{host} = join " | ", $host->all_hostnames();
	
		#------------------------------------------------------------------------
		#	iterate through the listed services and add certain service
		#	fields to the host info
		#------------------------------------------------------------------------
	
		# find all TCP / UDP service hashes and add to services list
		my @services;
		push @services, $host->tcp_service($_) foreach $host->tcp_open_ports();
		push @services, $host->udp_service($_) foreach $host->udp_open_ports();
	
		# copy relevant fields from Service object into the sql-entry hash
		my @service_infos;
		foreach my $service ( @services )
		{
			my %service_hash;
			$service_hash{$_} = $service->{$_} // 'null' foreach qw| port name product version extrainfo |;
			push @service_infos, \%service_hash;
		}
	
		$h{services} = \@service_infos;

		#------------------------------------------------------------------------
		#	iterate through the listed services and add certain service
		#	fields to the host info
		#------------------------------------------------------------------------

		# try to obtain smb info
		if( exists $host->{hostscript}->{'smb-os-discovery'}->{contents} )
		{
			my %smb_hash;
			my $smb_info = $host->{hostscript}->{'smb-os-discovery'}->{contents};

			my @smb_fields = qw| os fqdn forest_dns |;

			foreach( @smb_fields )
			{
				$smb_hash{$_} = $smb_info->{$_} // undef;
			}

			$h{smb} = \%smb_hash;
		}
		elsif( exists $host->{hostscript}->{'smb-os-discovery'}->{output} )
		{
			my %smb_hash;
			$smb_hash{output} = $host->{hostscript}->{'smb-os-discovery'}->{output};

			$h{smb} = \%smb_hash;
		}
		else
		{
			$h{smb} = undef;
		}

		# try to obtain 100-confidence OS guesses
		if( defined $host->{os}->{osmatch_name_accuracy} && $host->{os}->{osmatch_name_accuracy}->[0] eq '100' )
		{
			$h{os_guess} = $host->{os}->{osmatch_name}->[0];
		}
		else
		{
			$h{os_guess} = undef;
		}
	
		#------------------------------------------------------------------------
		#	look through a few select fields to try to determine
		#	device type and OS flavor
		#------------------------------------------------------------------------

		device_type_try( \%h );
	
		push @host_info, \%h;

		progress( scalar @host_info, scalar @hosts );
	}
	progress_done(sprintf("Completed info for %d hosts", scalar @host_info));

	# remove large variables from memory
	return \@host_info;
}

#--------------------------------------------------------------------------------
#	function to have each service for each machine on a separate
#	'row' so that linear searches for ports can be run on the data
#	without having to index into the hash
#--------------------------------------------------------------------------------

sub separate_services( $ )
{
	my @service_list;

	# pull out the list of host info
	my @host_info = @{ $_[0] };

	my $done = 0;
	progress_set_stage("Separating unique services");
	foreach my $host ( @host_info )
	{
		# pull out information common to all services on this host
		my $hash2flatten;
		foreach( keys $host )
		{
			$hash2flatten->{$_} = $host->{$_} unless $_ eq 'services';
		}

		my $flat_hash = flatten( $hash2flatten );

		# iterate through the services and create a 'row' for each
		foreach my $service ( @{$host->{services}} )
		{
			my %service_hash = %$flat_hash;
			$service_hash{$_} = $service->{$_} foreach( keys $service );

			while( my ($k,$v) = each %service_hash )
			{
				if( defined $v )
				{
					my $fixed = lc $v;
					$fixed = $1 if $fixed =~ /^\s*\((.*)\)\s*$/;
					$service_hash{$k} = $fixed;
				}
				else
				{
					delete $service_hash{$k};
				}
			}

			push @service_list, \%service_hash;
		}

		# try to standardize the values for each of these
		progress( $done, scalar @host_info );
		++$done;
	}
	progress_done(sprintf("Processed %d services", scalar @service_list));

	return \@service_list;
}

sub check_guesses( $$ )
{
	my @hosts = @{ shift @_ };
	my @all_hosts = @{ shift @_ };

	my $completed_guesses = 0;
	foreach my $host ( @hosts )
	{
		if( defined $host->{device_type} || defined $host->{os_flavor} )
		{
			++$completed_guesses;
		}
	}

	#print color 'orange';
	my $percentage = int($completed_guesses / scalar(@hosts) * 100);
	printf "Completed guesses for %d / %d hosts (%d%%)\n", $completed_guesses,
		scalar @hosts, $percentage;
}

# write to CSV with 1 host per line, each host service on the same line
sub csv_write_1( $ )
{
	my @services = @{ shift @_ };

	# first, find the longest list of fields
	my %fields;
	foreach( @services )
	{
		my @service_fields = keys $_;
		foreach( @service_fields )
		{
			$fields{$_} = 1;
		}
	}

	my %hosthash;
	foreach( @services )
	{
		my $ip = $_->{ip};
		unless( exists $hosthash{$ip} )
		{
			$hosthash{$ip} = [];
		}

		push @{ $hosthash{$ip} }, $_;
	}

	# print a header containing the names of the fields
	my @fields = sort( keys %fields );
	print join( ',', @fields ) . "\n";

	# for each host, print a single line containing all
	# active services for that host
	while( my($ip, $services) = each %hosthash )
	{

		# pull out the general host info common to all services
		my $hoststring = "";
		my @service_list = @{ $services };

		my $first = $service_list[0];
		my @host_fields = qw| ip host device_type os_flavor smb.forest smb.fqdn smb.os |;
		my @host_values = map { $first->{$_} // 'null' } @host_fields;

		$hoststring .= join ',', @host_values;
		$hoststring .= ',';
		
		# start appending the info for each of the services
		my @service_fields = qw| port name product version extrainfo |;
		foreach my $service ( @service_list )
		{
			my @service_values = map { $service->{$_} } @service_fields;
			$hoststring .= join ',', @service_values;
		}

		print $hoststring . "\n";
	}
}

# write to CSV with 1 service per line
sub csv_write_2( $ )
{
	my @field_order = qw| ip host device_type os_flavor port name product version extrainfo method |;

	my @services = @{ $_[0] };

	# open a file and print out the column headers
	open DUMP, '>', 'nmap_results.txt' or die $!;
	print DUMP join('~', @field_order) . "\n";

	# iterate through the services and print the relevant info for each
	foreach my $service ( @services )
	{
		my @service_info;
		foreach( @field_order )
		{
			my $result = $service->{$_} // 'null';
			$result = 'null' if $result eq '';
			push @service_info, $result;
		}
		print DUMP join('~', @service_info) . "\n";
	}

	close DUMP;
}

# code block to run when script is called directly
unless( caller )
{
	# find all xml files corresponding to nmap scan data
	my $xml_files = find_xml_files();

	# read the finished-scan xml files into a list
	my $file_texts = read_xml_files( $xml_files );
	undef $xml_files;

	# use the Nmap::Parser module to find all hosts
	# associated with each scan
	my $hosts = find_hosts( $file_texts );
	undef $file_texts;

	# go through each host hash and extract the desired
	# information into a separate hash for our use
	my $host_info = parse_hosts( $hosts );
	#undef $hosts;

	# separate each service into its own 'row' and
	# flatten the hash containing the host info
	my $service_list = separate_services( $host_info );

	# write out to file as CSV
	csv_write_2( $service_list );

	# determine how well the os-guess logic worked
	print "Script complete! Check your results in 'nmap_results.csv'\n";
	check_guesses( $host_info, $hosts );
}

