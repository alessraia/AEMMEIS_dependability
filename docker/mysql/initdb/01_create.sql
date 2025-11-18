DROP database if exists aemmetsw;
create database aemmetsw;
use aemmetsw;

Create table Sede (
                      idSede int not null auto_increment,
                      citta varchar(250) not null,
                      via varchar(250) not null,
                      numeroCivico int not null,
                      cap char(5) not null,
                      primary key (idSede)
);

Create table Libro (
                       isbn char(13) primary key,
                       titolo varchar(250) not null,
                       genere varchar(250) not null,
                       annoPubblicazione char(4) not null,
                       prezzo double not null,
                       sconto int default 0,
                       trama text,
                       immagine varchar(255),
                       disponibile TINYINT DEFAULT 1
);

Create table Presenza (
                          idSede int not null,
                          isbn char(13) not null,
                          primary key( idSede, isbn),
                          foreign key( idSede ) references Sede( idSede ),
                          foreign key( isbn ) references Libro( isbn )
);

Create table Autore (
                        cf char(16) primary key,
                        nome char(20) not null,
                        cognome char(20) not null
);

Create table Scrittura (
                           cf char(16) not null,
                           isbn char(13) not null,
                           primary key( cf, isbn),
                           foreign key( cf ) references Autore( cf ),
                           foreign key( isbn ) references Libro( isbn )
);

Create table Reparto (
                         idReparto int not null AUTO_INCREMENT,
                         nome varchar(250) not null,
                         descrizione text,
                         immagine varchar(250) not null,
                         primary key( idReparto )
);

Create table Appartenenza (
                              idReparto int not null,
                              isbn char(13) not null,
                              primary key( idReparto, isbn),
                              foreign key( idReparto ) references Reparto( idReparto ),
                              foreign key( isbn ) references Libro( isbn )
);

Create table Gestore (
                         matricola char(7) primary key,
                         stipendio double not null
);

Create table Utente (
                        nomeUtente varchar(50) not null,
                        email varchar(50) not null,
                        codiceSicurezza varchar(250) not null,
                        tipo varchar(15) not null,
                        primary key (email)
);

Create table Telefono (
                          numeroTelefono char(15) primary key,
                          email varchar(50) references Utente( email )
);

Create table WishList (
                          email varchar(50) not null,
                          isbn char(13) not null,
                          primary key( email, isbn),
                          foreign key( email ) references Utente( email ),
                          foreign key( isbn ) references Libro( isbn )
);

Create table Tessera (
                         numero char(4) primary key,
                         dataCreazione Date not null,
                         dataScadenza Date not null,
                         punti int default 50,
                         email varchar(50) references Utente( email )
);

Create table Ordine (
                        idOrdine char(5) primary key,
                        costo double not null,
                        indirizzoSpedizione varchar(250) not null,
                        citta varchar(250) not null,
                        puntiOttenuti int default 0,
                        puntiSpesi int default 0,
                        dataArrivo Date,
                        dataEffettuazione Date not null,
                        stato varchar(20) not null,
                        matricola char(7) not null references Gestore( matricola ),
                        email varchar(50) not null references Utente( email )
);

Create table Carrello (
                          idCarrello char(5) primary key,
                          totale double not null,
                          email varchar(50) not null references Utente( email )
);

Create table RigaOrdine (
                            idOrdine char(5) not null,
                            isbn char(13) not null,
                            prezzoUnitario double not null,
                            quantita int default 1,
                            primary key( idOrdine, isbn),
                            foreign key( idOrdine ) references Ordine( idOrdine ),
                            foreign key( isbn ) references Libro( isbn )
);

Create table RigaCarrello (
                              idCarrello char(5) not null,
                              isbn char(13) not null,
                              quantita int default 1,
                              primary key( idCarrello, isbn),
                              foreign key( idCarrello ) references Carrello( idCarrello ),
                              foreign key( isbn ) references Libro( isbn )
);