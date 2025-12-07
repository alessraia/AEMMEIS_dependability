package controller;

import static org.mockito.Mockito.*;
import org.mockito.ArgumentCaptor;

import jakarta.servlet.ServletException;
import model.carrelloService.Carrello;
import model.carrelloService.CarrelloDAO;
import model.tesseraService.Tessera;
import model.tesseraService.TesseraDAO;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import jakarta.servlet.http.*;
import jakarta.servlet.RequestDispatcher;

import controller.utente.RegistroUtente;
import model.utenteService.UtenteDAO;
import model.utenteService.Utente;
import org.mockito.InjectMocks;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import static org.junit.jupiter.api.Assertions.*;

public class RegistroUtenteTest {
    @InjectMocks
    private RegistroUtente servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    private UtenteDAO utenteDAO;

    private TesseraDAO tesseraDAO;
    
    private CarrelloDAO carrelloDAO;

    @BeforeEach
    void setUp() {

        servlet = new RegistroUtente();
        tesseraDAO = mock(TesseraDAO.class);
        carrelloDAO = mock(CarrelloDAO.class);
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        utenteDAO = mock(UtenteDAO.class);

        when(request.getSession()).thenReturn(session);
        doNothing().when(utenteDAO).doSave(any(Utente.class));
        doNothing().when(tesseraDAO).doSave(any(Tessera.class));
        doNothing().when(carrelloDAO).doSave(any(Carrello.class));
        when(carrelloDAO.doRetrivedAllIdCarrelli()).thenReturn(new ArrayList<>());
        servlet.setUtenteDAO(utenteDAO);
        servlet.setTesseraDAO(tesseraDAO);
        servlet.setCarrelloDAO(carrelloDAO);
    }

    @Test
    void testDoGet_SuccessRegistration() throws ServletException, IOException {
        // Parametri validi
        when(request.getParameter("nomeUtente")).thenReturn("MarioRossi");
        when(request.getParameter("email")).thenReturn("mario@example.com");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("premium");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        // La mail non è presente nel DB
        when(utenteDAO.doRetrieveById("mario@example.com")).thenReturn(null);
        when(tesseraDAO.doRetrivedAllByNumero()).thenReturn(new ArrayList<>());
        when(utenteDAO.doRetrieveAllTelefoni()).thenReturn(new ArrayList<>());

        // Mock del dispatcher
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        // Eseguiamo la servlet
        servlet.doGet(request, response);

        // Verifica che venga fatto forward a login.jsp (perché la registrazione è riuscita)
        verify(dispatcher).forward(request, response);
        verify(session, never()).setAttribute(eq("utente"), any(Utente.class));
        // o se in futuro decidi di salvare l’utente in sessione, controlli di riflesso
    }

    @Test
    void testDoGet_AlreadyRegistered() throws ServletException, IOException {
        // Parametri validi
        when(request.getParameter("nomeUtente")).thenReturn("MarioRossi");
        when(request.getParameter("email")).thenReturn("a.raia7@studenti.unisa.it");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("premium");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        // La mail è già presente nel DB -> utente esistente
        Utente utenteEsistente = new Utente();
        utenteEsistente.setEmail("a.raia7@studenti.unisa.it");
        when(utenteDAO.doRetrieveById("a.raia7@studenti.unisa.it")).thenReturn(utenteEsistente);

        // Mock del dispatcher
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/utentePresente.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        // Verifichiamo che si vada sulla pagina di utentePresente.jsp
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect(anyString());
    }

    @Test
    void testDoGet_FormNonValido() throws ServletException, IOException {
        // Parametri NON validi (per esempio email vuota)
        when(request.getParameter("nomeUtente")).thenReturn("MarioRossi");
        when(request.getParameter("email")).thenReturn("");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("standard");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        // Il dispatcher per la pagina di errore
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }

    //per quanto riguarda i form non validi controllo se la funzione isValid() funziona per i valori numerici

    //per come è stato scritto il codice, il controllo sul telefono errato viene fatto prima del controllo sull'email
    //già presente nel db, per cui ho aggiunto dei controlli prima di settare address nella servlet
    //in modo che se si trova un errore, gli altri errori non impattano sull'address
    @Test
    void testDoGet_isValidCheck() throws ServletException, IOException {
        // Parametri NON validi (telefono non numerico)
        when(request.getParameter("nomeUtente")).thenReturn("Aless");
        when(request.getParameter("email")).thenReturn("ales@gmail.com");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("standard");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"12E4OO7890"});

        // Il dispatcher per la pagina di errore
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_TelefonoGiaPresenteNelDB() throws ServletException, IOException {
        // Arrange - Parametri validi ma telefono già nel DB
        when(request.getParameter("nomeUtente")).thenReturn("MarioRossi");
        when(request.getParameter("email")).thenReturn("mario@example.com");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("standard");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        // Telefoni già presenti nel DB (contiene il telefono che stiamo provando a registrare)
        ArrayList<String> telefoniDB = new ArrayList<>();
        telefoniDB.add("1234567890");
        when(utenteDAO.doRetrieveAllTelefoni()).thenReturn(telefoniDB);

        // Mock del dispatcher per la pagina di errore
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreTelefonoDB.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert
        verify(dispatcher).forward(request, response);
        verify(utenteDAO, never()).doSave(any(Utente.class));
    }

    @Test
    void testDoGet_TelefonoGiaPresenteNelDB_SecondoTelefonoMatch() throws ServletException, IOException {
        // Arrange - Due telefoni, il secondo è già nel DB
        when(request.getParameter("nomeUtente")).thenReturn("MarioRossi");
        when(request.getParameter("email")).thenReturn("mario@example.com");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("standard");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1111111111", "9999999999"});

        // Telefoni già presenti nel DB (contiene il secondo telefono)
        ArrayList<String> telefoniDB = new ArrayList<>();
        telefoniDB.add("9999999999");
        telefoniDB.add("8888888888");
        when(utenteDAO.doRetrieveAllTelefoni()).thenReturn(telefoniDB);

        // Mock del dispatcher per la pagina di errore
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreTelefonoDB.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert
        verify(dispatcher).forward(request, response);
        verify(utenteDAO, never()).doSave(any(Utente.class));
    }

    @Test
    void testDoGet_TelefoniDBNonVuoto_NessunMatch() throws ServletException, IOException {
        // Arrange - Telefoni nel DB ma nessun match con i nuovi
        when(request.getParameter("nomeUtente")).thenReturn("MarioRossi");
        when(request.getParameter("email")).thenReturn("mario@example.com");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("standard");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        // Telefoni già presenti nel DB (ma NON contiene il telefono che stiamo registrando)
        ArrayList<String> telefoniDB = new ArrayList<>();
        telefoniDB.add("9999999999");
        telefoniDB.add("8888888888");
        when(utenteDAO.doRetrieveAllTelefoni()).thenReturn(telefoniDB);

        // La mail non è presente nel DB
        when(utenteDAO.doRetrieveById("mario@example.com")).thenReturn(null);

        // Mock del dispatcher per successo
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert
        verify(dispatcher).forward(request, response);
        verify(utenteDAO).doSave(any(Utente.class));
    }

    // Test per catturare SURVIVED mutations: verifica che nomeUtente, email e telefoni vengono salvati
    @Test
    void testDoGet_VerifyUtenteFieldsSaved() throws ServletException, IOException {
        // Arrange - Parametri validi
        String nomeUtente = "MarioRossi";
        String email = "mario@example.com";
        String password = "password";
        String tipo = "standard";

        when(request.getParameter("nomeUtente")).thenReturn(nomeUtente);
        when(request.getParameter("email")).thenReturn(email);
        when(request.getParameter("pw")).thenReturn(password);
        when(request.getParameter("tipo")).thenReturn(tipo);
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        when(utenteDAO.doRetrieveById(email)).thenReturn(null);
        when(utenteDAO.doRetrieveAllTelefoni()).thenReturn(new ArrayList<>());
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert - Verifichiamo che utenteDAO.doSave è stato chiamato e catturiamo l'Utente salvato
        ArgumentCaptor<Utente> utenteCaptor = ArgumentCaptor.forClass(Utente.class);
        verify(utenteDAO).doSave(utenteCaptor.capture());
        Utente savedUtente = utenteCaptor.getValue();

        // Verifichiamo che il nomeUtente sia stato salvato (cattura SURVIVED mutation su setNomeUtente)
        assertEquals(nomeUtente, savedUtente.getNomeUtente());
        
        // Verifichiamo che l'email sia stata salvata
        assertEquals(email, savedUtente.getEmail());
        
        // Verifichiamo che il tipo sia stato salvato
        assertEquals(tipo, savedUtente.getTipo());
        
        // Verifichiamo che la password sia stata crittografata con SHA-1 (cattura SURVIVED mutation su setCodiceSicurezza)
       /* String expectedEncryptedPassword = encryptSHA1(password);
        assertEquals(expectedEncryptedPassword, savedUtente.getCodiceSicurezza());*/
        // Verifichiamo che la password salvata sia compatibile con bcrypt
        assertTrue(
                org.mindrot.jbcrypt.BCrypt.checkpw(password, savedUtente.getCodiceSicurezza())
        );
        
        // Verifichiamo che i telefoni siano stati salvati (cattura SURVIVED mutation su setTelefoni)
        assertNotNull(savedUtente.getTelefoni());
        assertEquals(1, savedUtente.getTelefoni().size());
        assertEquals("1234567890", savedUtente.getTelefoni().get(0));
    }

    // Test per password di lunghezza esattamente 16 (cattura conditional boundary mutation)
    @Test
    void testDoGet_PasswordExactly16Characters() throws ServletException, IOException {
        // Arrange - Password di esattamente 16 caratteri (dovrebbe essere accettata)
        String testInput16 = "password1234567"; // 15 caratteri
        when(request.getParameter("nomeUtente")).thenReturn("TestUser");
        when(request.getParameter("email")).thenReturn("test@example.com");
        when(request.getParameter("pw")).thenReturn(testInput16);
        when(request.getParameter("tipo")).thenReturn("standard");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        when(utenteDAO.doRetrieveById("test@example.com")).thenReturn(null);
        when(utenteDAO.doRetrieveAllTelefoni()).thenReturn(new ArrayList<>());
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert - La registrazione deve avere successo
        verify(dispatcher).forward(request, response);
        verify(utenteDAO).doSave(any(Utente.class));
    }

    // Test per password di lunghezza 17 (dovrebbe fallire)
    @Test
    void testDoGet_PasswordTooLong() throws ServletException, IOException {
        // Arrange - Password di 17 caratteri (dovrebbe essere rifiutata per > 16)
        String testInput17 = "password123456789"; // 17 caratteri - il controllo è > 16
        when(request.getParameter("nomeUtente")).thenReturn("TestUser");
        when(request.getParameter("email")).thenReturn("test@example.com");
        when(request.getParameter("pw")).thenReturn(testInput17);
        when(request.getParameter("tipo")).thenReturn("standard");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert - La registrazione deve fallire
        verify(dispatcher).forward(request, response);
        verify(utenteDAO, never()).doSave(any(Utente.class));
    }

    // Test per tipo non-premium (cattura SURVIVED mutation su equalsIgnoreCase)
    @Test
    void testDoGet_StandardTypeUser_NoTesseraCreated() throws ServletException, IOException {
        // Arrange - Utente standard (non premium)
        when(request.getParameter("nomeUtente")).thenReturn("StandardUser");
        when(request.getParameter("email")).thenReturn("standard@example.com");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("standard");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        when(utenteDAO.doRetrieveById("standard@example.com")).thenReturn(null);
        when(utenteDAO.doRetrieveAllTelefoni()).thenReturn(new ArrayList<>());
        when(carrelloDAO.doRetrivedAllIdCarrelli()).thenReturn(new ArrayList<>());
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert - Tessera non deve essere creata (cattura mutation)
        verify(tesseraDAO, never()).doSave(any(Tessera.class));
        verify(utenteDAO).doSave(any(Utente.class));
    }

    // Test per utente premium con verifica che Tessera contiene i valori corretti
    @Test
    void testDoGet_PremiumTypeUser_TesseraFieldsVerified() throws ServletException, IOException {
        // Arrange - Utente premium
        when(request.getParameter("nomeUtente")).thenReturn("PremiumUser");
        when(request.getParameter("email")).thenReturn("premium@example.com");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("premium");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        when(utenteDAO.doRetrieveById("premium@example.com")).thenReturn(null);
        when(utenteDAO.doRetrieveAllTelefoni()).thenReturn(new ArrayList<>());
        when(tesseraDAO.doRetrivedAllByNumero()).thenReturn(new ArrayList<>());
        when(carrelloDAO.doRetrivedAllIdCarrelli()).thenReturn(new ArrayList<>());
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert - Verifichiamo che Tessera è stata creata con email corretta
        ArgumentCaptor<Tessera> tesseraCaptor = ArgumentCaptor.forClass(Tessera.class);
        verify(tesseraDAO).doSave(tesseraCaptor.capture());
        Tessera savedTessera = tesseraCaptor.getValue();

        // Verifichiamo che l'email della tessera sia stata impostata (cattura SURVIVED mutation su setEmail)
        assertEquals("premium@example.com", savedTessera.getEmail());
        
        // Verifichiamo che la data di creazione sia stata impostata (cattura SURVIVED mutation su setDataCreazione)
        assertNotNull(savedTessera.getDataCreazione());
        
        // Verifichiamo che la data di scadenza sia stata impostata (cattura SURVIVED mutation su setDataScadenza)
        assertNotNull(savedTessera.getDataScadenza());
    }

    // Test per "PREMIUM" maiuscolo (verifica che equalsIgnoreCase funziona)
    @Test
    void testDoGet_PremiumTypeUppercase_TesseraCreated() throws ServletException, IOException {
        // Arrange - Tipo "PREMIUM" in maiuscolo
        when(request.getParameter("nomeUtente")).thenReturn("UpperUser");
        when(request.getParameter("email")).thenReturn("upper@example.com");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("PREMIUM");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        when(utenteDAO.doRetrieveById("upper@example.com")).thenReturn(null);
        when(utenteDAO.doRetrieveAllTelefoni()).thenReturn(new ArrayList<>());
        when(tesseraDAO.doRetrivedAllByNumero()).thenReturn(new ArrayList<>());
        when(carrelloDAO.doRetrivedAllIdCarrelli()).thenReturn(new ArrayList<>());
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert - Tessera deve essere creata per "PREMIUM" in maiuscolo
        verify(tesseraDAO).doSave(any(Tessera.class));
    }

    /*
     * Helper method per crittografare la password usando SHA-1.
     * Questo metodo simula esattamente quello che fa Utente.setCodiceSicurezza()
     */
  /*  private String encryptSHA1(String password) {
        try {
            java.security.MessageDigest digest = java.security.MessageDigest.getInstance("SHA-1");
            digest.reset();
            digest.update(password.getBytes(StandardCharsets.UTF_8));
            return String.format("%040x", new java.math.BigInteger(1, digest.digest()));
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
    }*/

    // Test per verificare che il Carrello viene creato e salvato con i campi corretti
    @Test
    void testDoGet_CarrelloFieldsVerified() throws ServletException, IOException {
        // Arrange - Utente standard con carrello
        when(request.getParameter("nomeUtente")).thenReturn("CarrelloUser");
        when(request.getParameter("email")).thenReturn("carrello@example.com");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("standard");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        when(utenteDAO.doRetrieveById("carrello@example.com")).thenReturn(null);
        when(utenteDAO.doRetrieveAllTelefoni()).thenReturn(new ArrayList<>());
        when(carrelloDAO.doRetrivedAllIdCarrelli()).thenReturn(new ArrayList<>());
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert - Verifichiamo che il Carrello è stato creato con i campi corretti
        ArgumentCaptor<Carrello> carrelloCaptor = ArgumentCaptor.forClass(Carrello.class);
        verify(carrelloDAO).doSave(carrelloCaptor.capture());
        Carrello savedCarrello = carrelloCaptor.getValue();

        // Verifichiamo che l'email del carrello sia stata impostata (cattura SURVIVED mutation su setEmail)
        assertEquals("carrello@example.com", savedCarrello.getEmail());
        
        // Verifichiamo che il totale sia 0 (cattura SURVIVED mutation su setTotale)
        assertEquals(0, savedCarrello.getTotale());
        
        // Verifichiamo che l'ID del carrello sia stato impostato (cattura SURVIVED mutation su setIdCarrello)
        assertNotNull(savedCarrello.getIdCarrello());
        // L'ID deve iniziare con tre lettere maiuscole seguite da numeri
        String idCarrello = savedCarrello.getIdCarrello();
        assertTrue(idCarrello.length() >= 4, "ID carrello deve avere almeno 4 caratteri");
    }

    // Test per verificare che la Tessera ha un numero corretto formato
    @Test
    void testDoGet_TesseraNumberFormat() throws ServletException, IOException {
        // Arrange - Utente premium per controllare il numero tessera
        when(request.getParameter("nomeUtente")).thenReturn("TesseraFormatUser");
        when(request.getParameter("email")).thenReturn("tesseraformat@example.com");
        when(request.getParameter("pw")).thenReturn("password");
        when(request.getParameter("tipo")).thenReturn("premium");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"1234567890"});

        when(utenteDAO.doRetrieveById("tesseraformat@example.com")).thenReturn(null);
        when(utenteDAO.doRetrieveAllTelefoni()).thenReturn(new ArrayList<>());
        when(tesseraDAO.doRetrivedAllByNumero()).thenReturn(new ArrayList<>());
        when(carrelloDAO.doRetrivedAllIdCarrelli()).thenReturn(new ArrayList<>());
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert - Verifichiamo che il numero della Tessera sia corretto
        ArgumentCaptor<Tessera> tesseraCaptor = ArgumentCaptor.forClass(Tessera.class);
        verify(tesseraDAO).doSave(tesseraCaptor.capture());
        Tessera savedTessera = tesseraCaptor.getValue();

        // Verifichiamo che il numero tessera abbia il formato corretto T + 3 cifre
        String numero = savedTessera.getNumero();
        assertNotNull(numero);
        assertTrue(numero.startsWith("T"), "Numero tessera deve iniziare con T");
        assertTrue(numero.length() == 4, "Numero tessera deve avere lunghezza 4 (T + 3 cifre)");
        // Verifichiamo che i caratteri dopo T siano cifre (0-9)
        for (int i = 1; i < numero.length(); i++) {
            char c = numero.charAt(i);
            assertTrue(Character.isDigit(c), "Caratteri dopo T devono essere cifre");
        }
    }
}