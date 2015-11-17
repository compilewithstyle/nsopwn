#!/usr/bin/env perl 

#--------------------------------------------------------------------------------
#  [Author]:
#  	Written by Nicholas Siow | n.siow@wustl.edu
#  
#  [Description]:
#  	Parses fastnmap output and builds an easily-searchable
#  	database using that information
#  
#  [Revision History]:
#  	2014-12-11	broke script into subroutines, added &device_type_try
#  			that will look at various fields to try to determine
#  			OS info / identity of the device
#  	2014-06-30	finished script, tested and seems to be working.
#  	2014-06-27	switched to perl from python, better nmap-parsing lib
#  
#  [Todo]:
#	+ check the validity of the OS guesses
#  	[done] look for additional ways to determine the device info
#--------------------------------------------------------------------------------

use strict;
use warnings;

use DBI;
use JSON;
use File::Slurp;
use Tie::IxHash;
use Data::Dumper;
use Nmap::Parser;
use Term::ANSIColor;
use Hash::Flatten qw| flatten |;
use feature 'say';

# turn on STDOUT autoflush
$| = 1;

my $TEST = grep { $_ eq '--test' } @ARGV;
my $TESTAMOUNT = 500;
my $TABLENAME = 'nmap';

# check the supplied arguments and read in the nmap results
if( scalar @ARGV == 0 )
{
	print "Please enter a valid log directory.\n";
	print "Usage: ./nsopwn [LOGDIRS...]\n";
	exit(1);
}

foreach( @ARGV )
{
	unless( defined $_ && -e $_ )
	{
		printf "Invalid log directory: %s\n", $_;
		exit(1);
	}
}

#--------------------------------------------------------------------------------
#	helper function to print progress text
#--------------------------------------------------------------------------------

my %progress_hash;
sub progress( $$ )
{
	my $progress_string = shift;
	my $total_todo      = shift;

	my $done = $progress_hash{$progress_string} // 0;

	my $am_finished = $total_todo - $done == 1 ? 1 : 0;

	$am_finished ? print color 'green' : print color 'red';

	printf "\r" . $progress_string, $done+1, $total_todo;

	print color 'reset';

	++$progress_hash{$progress_string};

	print "\n" if $am_finished;
}

#--------------------------------------------------------------------------------
#	function to compare an OS / device string against a list of known
#	products to try to add a standardized tag
#--------------------------------------------------------------------------------

my %known_products = (
	windows   => 'windows',
	microsoft => 'windows',
	linux     => 'linux',
	ubuntu    => 'linux',
	fedora    => 'linux',
	centos    => 'linux',
	unix      => 'linux',
	'red hat' => 'linux',
	apple	  => 'apple',
	solaris   => 'solaris',
	printer   => 'printer',
	laserjet  => 'printer',
	switch    => 'switch',
	camera    => 'camera',
	vxworks   => 'vxworks',
	firewall  => 'firewall',
#	osx       => 'mac osx',
#	cisco     => 'cisco',
);

sub os_info_search( $ )
{
	my $os_string = shift;

	foreach( keys %known_products )
	{
		return $known_products{$_} if $os_string =~ /$_/i;
	}

	#return $os_string;
	return '';
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

	if( defined $host->{os_guess} && ($host->{os_guess} =~ /apple/i || $host->{os_guess} !~ / or /i) )
	{
		$host->{device_type} = os_info_search( $host->{os_guess} );
		$host->{os_flavor} = lc $host->{os_guess};
		$host->{method} = 1;
		return if $host->{device_type} ne '';
	}

	#------------------------------------------------------------------------
	#	Attempt #2 -- use SMB data if that exists
	#------------------------------------------------------------------------

	if( defined $host->{smb}->{os} )
	{
		$host->{device_type} = os_info_search( $host->{smb}->{os} );
		$host->{os_flavor}   = lc $host->{smb}->{os};
		$host->{method} = 2;
		return if $host->{device_type} ne '';
	}

	#------------------------------------------------------------------------
	#	Attempt #3 -- use port 80/443 webserver identification
	#------------------------------------------------------------------------

	if( grep { $_->{port} eq 80 } @{$host->{services}} )
	{
		my ($service) = grep { $_->{port} eq '80' } @{$host->{services}};
		$host->{device_type} = os_info_search( Dumper($service) );
		if( $service->{extrainfo} ne '' ) {
			$host->{os_flavor} = $service->{extrainfo};
		}
		elsif( $service->{product} ne '' ) {
			$host->{os_flavor} = $service->{product};
		}
		$host->{method} = 3;
		return if $host->{device_type} ne '';
	}
	if( grep { $_->{port} eq 443 } @{$host->{services}} )
	{
		my ($service) = grep { $_->{port} eq '443' } @{$host->{services}};
		$host->{device_type} = os_info_search( Dumper($service) );
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

	if( grep { $_->{port} eq 22 } @{$host->{services}} )
	{
		my ($service) = grep { $_->{port} eq '22' } @{$host->{services}};
		$host->{os_flavor} = os_info_search( $service->{extrainfo} );
		$host->{device_type} = $host->{os_flavor} // undef;
		$host->{method} = 4;
		return if $host->{device_type} ne '';
	}

	#------------------------------------------------------------------------
	#	Attempt #5 -- use microsoft product info
	#------------------------------------------------------------------------

	foreach my $service ( @{$host->{services}} )
	{
		if( exists $service->{product} && os_info_search($service->{product}) eq 'windows' )
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


	$host->{device_type} = undef;
	$host->{os_flavor}   = undef;
	$host->{method} = -1;
}

#--------------------------------------------------------------------------------
#	function to recursively find all XML files in the given base directory
#--------------------------------------------------------------------------------

sub find_xml_files()
{
	my @xml_files;
	foreach my $topdir ( @ARGV )
	{
		chomp ( my @files = `find $topdir -name *xml` );
		print color 'red';
		print "Looking for XML files...\n";
		print color 'green';
		printf "\tfound %d files in directory %s\n", scalar @files, $topdir;
		print color 'reset';
		push @xml_files, $_ foreach @files;
	}

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
	my @finished_scans;
	foreach( @files )
	{
		my @lines = read_file($_);
		push @finished_scans, $_ if grep { /\/nmaprun/ } @lines;
	
		progress( "Reading in XML files: [%5d / %5d]", scalar @files );

		last if $TEST && scalar @finished_scans == $TESTAMOUNT;
	}
	
	die "Found no finished nmap scans in dir: $ARGV[0]" if scalar @finished_scans == 0;

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
	my @hosts;
	foreach my $file ( @finished_scans )
	{
		$np->parsefile($file);
	
		# only pull in hosts that were up
		push @hosts, $_ foreach ($np->all_hosts('up'));
	
		progress( "Parsing nmap results: [%5d / %5d]", scalar @finished_scans );
	}
	
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
		#
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
		#
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

		progress( "Parsing nmap host data: [%5d / %5d]", scalar @hosts );
	}

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

		progress( "Separating services: [%5d / %5d]", scalar @host_info );
	}

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
        print color 'red';
	printf "Completed guesses for %5d / %5d hosts\n", $completed_guesses, scalar @hosts;
	print color 'reset';
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
	check_guesses( $host_info, $hosts );
}

