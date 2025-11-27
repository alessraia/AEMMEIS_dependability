package controller.utente.ordine;

import controller.utente.ordine.OrdineServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.carrelloService.CarrelloDAO;
import model.carrelloService.RigaCarrello;
import model.carrelloService.RigaCarrelloDAO;
import model.gestoreService.Gestore;
import model.gestoreService.GestoreDAO;
import model.libroService.Libro;
import model.ordineService.Ordine;
import model.ordineService.OrdineDAO;
import model.tesseraService.TesseraDAO;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;

import java.io.IOException;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class OrdineServletTest {

    private OrdineServlet servletUnderTest;
    private RigaCarrelloDAO rigaCarrelloDAO;
    private CarrelloDAO carrelloDAO;
    private OrdineDAO ordineDAO;
    private TesseraDAO tesseraDAO;
    private GestoreDAO gestoreDAO;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servletUnderTest = new OrdineServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        ordineDAO = mock(OrdineDAO.class);
        carrelloDAO = mock(CarrelloDAO.class);
        rigaCarrelloDAO = mock(RigaCarrelloDAO.class);
        tesseraDAO = mock(TesseraDAO.class);
        gestoreDAO = mock(GestoreDAO.class);

        servletUnderTest.setOrdineDAO(ordineDAO);
        servletUnderTest.setCarrelloDAO(carrelloDAO);
        servletUnderTest.setRigaCarrelloDAO(rigaCarrelloDAO);
        servletUnderTest.setTesseraDAO(tesseraDAO);
        servletUnderTest.setGestoreDAO(gestoreDAO);
        doNothing().when(ordineDAO).doSave(any(Ordine.class));
        
        // Setup gestore with matricola for verification
        Gestore gestore = new Gestore();
        gestore.setMatricola("G001");
        when(gestoreDAO.doRetrivedAll()).thenReturn(List.of(gestore));
        
        when(request.getSession()).thenReturn(session);
    }

    /**
     * Flusso principale: Salvataggio ordine con successo -> redirect index.html
     * UC_GO_4.3 main scenario
     * 
     * IMPROVED: Now captures and verifies the Ordine object to kill SURVIVED mutations
     */
    @Test
    void testDoGet_Success() throws ServletException, IOException {
        // Utente standard
        Utente user = new Utente();
        user.setTipo("standard");
        user.setEmail("mario@example.com");
        when(session.getAttribute("utente")).thenReturn(user);

        // Parametri
        when(request.getParameter("indirizzo")).thenReturn("Via Roma 1");
        when(request.getParameter("citta")).thenReturn("Napoli");
        when(request.getParameter("punti")).thenReturn("0"); // se standard

        // righeDisponibili
        List<RigaCarrello> righeDisponibili = new ArrayList<RigaCarrello>();
        Libro libro = new Libro();
        libro.setIsbn("1111111111111");
        libro.setPrezzo(10.0);
        libro.setSconto(10);
        libro.setDisponibile(true);
        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setIdCarrello("2");
        rigaCarrello.setLibro(libro);
        rigaCarrello.setQuantita(2);
        righeDisponibili.add(rigaCarrello); // TOT = (10 - 10%)=9 *2=18

        when(ordineDAO.doRetrivedAllByIdOrdini()).thenReturn(new ArrayList<>());
        when(session.getAttribute("righeDisponibili")).thenReturn(righeDisponibili);

        // Carrello in session
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("C0001");
        carrello.setEmail("mario@example.com");
        List<RigaCarrello> righeCarrello = new ArrayList<RigaCarrello>(righeDisponibili);
        carrello.setRigheCarrello(righeCarrello);

        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(carrelloDAO.doRetriveByUtente("mario@example.com")).thenReturn(carrello);
        doNothing().when(rigaCarrelloDAO).deleteRigaCarrello(anyString(), anyString());

        // Esecuzione
        servletUnderTest.doGet(request, response);

        // Verifica che la servlet fa un redirect alla home
        verify(response).sendRedirect("index.html");
        verify(dispatcher, never()).forward(request, response);

        // ===== IMPROVEMENTS TO KILL SURVIVED MUTATIONS =====
        
        // Capture the Ordine object that was saved
        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);
        verify(ordineDAO).doSave(ordineCaptor.capture());
        Ordine savedOrdine = ordineCaptor.getValue();
        
        // KILL mutations on lines 84-85: verify setters were called correctly
        assertEquals("Via Roma 1", savedOrdine.getIndirizzoSpedizione(), "Indirizzo should be set");
        assertEquals("Napoli", savedOrdine.getCitta(), "Citta should be set");
        
        // KILL mutation on line 93: verify punti spesi
        assertEquals(0, savedOrdine.getPuntiSpesi(), "Punti spesi should be 0 for standard user");
        
        // KILL mutation on line 108: verify idOrdine was set
        assertNotNull(savedOrdine.getIdOrdine(), "IdOrdine should be set");
        assertTrue(savedOrdine.getIdOrdine().startsWith("T"), "IdOrdine should start with T");
        
        // KILL mutations on lines 120, 129: verify price calculations
        // Expected: (10.0 - 10%) * 2 = 9.0 * 2 = 18.0
        assertEquals(18.0, savedOrdine.getCosto(), 0.01, "Cost calculation should be correct");
        
        // KILL mutations on lines 117-118, 123-124: verify RigaOrdine was populated correctly
        assertNotNull(savedOrdine.getRigheOrdine(), "RigheOrdine should not be null");
        assertEquals(1, savedOrdine.getRigheOrdine().size(), "Should have 1 riga ordine");
        
        // Verify the RigaOrdine fields (kills setters mutations)
        assertEquals(savedOrdine.getIdOrdine(), savedOrdine.getRigheOrdine().get(0).getIdOrdine(), 
                "RigaOrdine idOrdine should match");
        assertEquals(libro, savedOrdine.getRigheOrdine().get(0).getLibro(), 
                "RigaOrdine libro should match");
        assertEquals(9.0, savedOrdine.getRigheOrdine().get(0).getPrezzoUnitario(), 0.01, 
                "RigaOrdine prezzoUnitario should be calculated correctly");
        assertEquals(2, savedOrdine.getRigheOrdine().get(0).getQuantita(), 
                "RigaOrdine quantita should match");
        
        // KILL mutations on lines 136-147: verify cart removal logic (DAO interaction)
        // The servlet should delete the riga from database when full quantity is ordered
        verify(rigaCarrelloDAO).deleteRigaCarrello(eq("1111111111111"), eq("C0001"));
        
        // Verify cart in session was updated (riga removed)
        assertEquals(0, carrello.getRigheCarrello().size(), 
                "Cart in session should be empty after ordering all items");
        
        // KILL mutation on line 157: verify punti ottenuti (should be 0 for standard user)
        assertEquals(0, savedOrdine.getPuntiOttenuti(), "Punti ottenuti should be 0 for standard user");
        
        // KILL mutation on line 176: verify email was set
        assertEquals("mario@example.com", savedOrdine.getEmail(), "Email should be set from utente");
        
        // KILL mutation on line 178: verify data effettuazione was set to today
        assertEquals(LocalDate.now(), savedOrdine.getDataEffettuazione(), 
                "DataEffettuazione should be set to today");
        
        // KILL mutation on line 182: verify stato was set
        assertEquals("In Lavorazione", savedOrdine.getStato(), "Stato should be 'In Lavorazione'");
        
        // KILL mutation on line 185: verify matricola was set (from gestore)
        assertNotNull(savedOrdine.getMatricola(), "Matricola should be set from gestore");
    }

    /**
     * TEST: Non-zero punti parameter
     * KILLS mutation on line 93: setPuntiSpesi with non-zero value
     * This ensures the setter is actually called (not just defaulting to 0)
     */
    @Test
    void testDoGet_WithPuntiSpesi() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        user.setEmail("test@example.com");
        when(session.getAttribute("utente")).thenReturn(user);

        when(request.getParameter("indirizzo")).thenReturn("Via Test");
        when(request.getParameter("citta")).thenReturn("Test");
        when(request.getParameter("punti")).thenReturn("5"); // NON-ZERO value

        Libro libro = new Libro();
        libro.setIsbn("TEST123");
        libro.setPrezzo(10.0);
        libro.setSconto(0);
        
        RigaCarrello riga = new RigaCarrello();
        riga.setLibro(libro);
        riga.setQuantita(1);
        riga.setIdCarrello("CART1");
        
        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga);

        Carrello carrello = new Carrello();
        carrello.setIdCarrello("CART1");
        carrello.setRigheCarrello(new ArrayList<>(righe));

        when(ordineDAO.doRetrivedAllByIdOrdini()).thenReturn(new ArrayList<>());
        when(session.getAttribute("righeDisponibili")).thenReturn(righe);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(carrelloDAO.doRetriveByUtente(anyString())).thenReturn(carrello);
        doNothing().when(rigaCarrelloDAO).deleteRigaCarrello(anyString(), anyString());

        servletUnderTest.doGet(request, response);

        ArgumentCaptor<Ordine> captor = ArgumentCaptor.forClass(Ordine.class);
        verify(ordineDAO).doSave(captor.capture());
        
        // CRITICAL: Verify non-zero value - if setter is removed, this will fail
        assertEquals(5, captor.getValue().getPuntiSpesi(), 
                "Punti spesi should be 5 (kills line 93 mutation)");
        
        // KILL mutation on line 157: even though value is 0, we must verify it was explicitly set
        assertEquals(0, captor.getValue().getPuntiOttenuti(), 
                "Punti ottenuti should be 0 for standard user (kills line 157 mutation)");
        
        // Verify cost calculation accounts for points: 10.0 - (5 * 0.10) = 9.50
        assertEquals(9.50, captor.getValue().getCosto(), 0.01, 
                "Cost should be reduced by punti spesi");
    }

    /**
     * TEST: Null punti parameter
     * KILLS mutations on line 91: null check conditionals
     */
    @Test
    void testDoGet_NullPuntiParameter() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        user.setEmail("test@example.com");
        when(session.getAttribute("utente")).thenReturn(user);

        when(request.getParameter("indirizzo")).thenReturn("Via Test");
        when(request.getParameter("citta")).thenReturn("Test");
        when(request.getParameter("punti")).thenReturn(null); // NULL

        Libro libro = new Libro();
        libro.setPrezzo(10.0);
        libro.setSconto(0);
        
        RigaCarrello riga = new RigaCarrello();
        riga.setLibro(libro);
        riga.setQuantita(1);
        
        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(new ArrayList<>(righe));

        when(ordineDAO.doRetrivedAllByIdOrdini()).thenReturn(new ArrayList<>());
        when(session.getAttribute("righeDisponibili")).thenReturn(righe);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(carrelloDAO.doRetriveByUtente(anyString())).thenReturn(carrello);

        servletUnderTest.doGet(request, response);

        ArgumentCaptor<Ordine> captor = ArgumentCaptor.forClass(Ordine.class);
        verify(ordineDAO).doSave(captor.capture());
        assertEquals(0, captor.getValue().getPuntiSpesi(), "Punti should default to 0 when null");
    }

    /**
     * TEST: Empty punti parameter
     * KILLS mutations on line 91: isEmpty check conditional
     */
    @Test
    void testDoGet_EmptyPuntiParameter() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        user.setEmail("test@example.com");
        when(session.getAttribute("utente")).thenReturn(user);

        when(request.getParameter("indirizzo")).thenReturn("Via Test");
        when(request.getParameter("citta")).thenReturn("Test");
        when(request.getParameter("punti")).thenReturn(""); // EMPTY

        Libro libro = new Libro();
        libro.setPrezzo(10.0);
        libro.setSconto(0);
        
        RigaCarrello riga = new RigaCarrello();
        riga.setLibro(libro);
        riga.setQuantita(1);
        
        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(new ArrayList<>(righe));

        when(ordineDAO.doRetrivedAllByIdOrdini()).thenReturn(new ArrayList<>());
        when(session.getAttribute("righeDisponibili")).thenReturn(righe);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(carrelloDAO.doRetriveByUtente(anyString())).thenReturn(carrello);

        servletUnderTest.doGet(request, response);

        ArgumentCaptor<Ordine> captor = ArgumentCaptor.forClass(Ordine.class);
        verify(ordineDAO).doSave(captor.capture());
        assertEquals(0, captor.getValue().getPuntiSpesi(), "Punti should default to 0 when empty");
    }

    /**
     * TEST: Cart with multiple items, ordering only one
     * KILLS mutation on line 147: loop boundary condition in cart removal
     */
    @Test
    void testDoGet_MultipleItemsInCart_OrderOnlyOne() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        user.setEmail("test@example.com");
        when(session.getAttribute("utente")).thenReturn(user);

        when(request.getParameter("indirizzo")).thenReturn("Via Test");
        when(request.getParameter("citta")).thenReturn("Test");
        when(request.getParameter("punti")).thenReturn("0");

        // Create two different books
        Libro libro1 = new Libro();
        libro1.setIsbn("BOOK1");
        libro1.setPrezzo(10.0);
        libro1.setSconto(0);
        
        Libro libro2 = new Libro();
        libro2.setIsbn("BOOK2");
        libro2.setPrezzo(15.0);
        libro2.setSconto(0);
        
        // righeDisponibili: only ordering libro1
        RigaCarrello rigaToOrder = new RigaCarrello();
        rigaToOrder.setLibro(libro1);
        rigaToOrder.setQuantita(1);
        rigaToOrder.setIdCarrello("CART1");
        
        List<RigaCarrello> righeDisponibili = new ArrayList<>();
        righeDisponibili.add(rigaToOrder);
        
        // Cart in session: has BOTH books
        RigaCarrello rigaCart1 = new RigaCarrello();
        rigaCart1.setLibro(libro1);
        rigaCart1.setQuantita(1);
        
        RigaCarrello rigaCart2 = new RigaCarrello();
        rigaCart2.setLibro(libro2);
        rigaCart2.setQuantita(1);

        Carrello carrello = new Carrello();
        carrello.setIdCarrello("CART1");
        List<RigaCarrello> righeCarrello = new ArrayList<>();
        righeCarrello.add(rigaCart1);
        righeCarrello.add(rigaCart2);  // Second item stays in cart
        carrello.setRigheCarrello(righeCarrello);

        when(ordineDAO.doRetrivedAllByIdOrdini()).thenReturn(new ArrayList<>());
        when(session.getAttribute("righeDisponibili")).thenReturn(righeDisponibili);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(carrelloDAO.doRetriveByUtente(anyString())).thenReturn(carrello);
        doNothing().when(rigaCarrelloDAO).deleteRigaCarrello(anyString(), anyString());

        servletUnderTest.doGet(request, response);

        // KILL mutation on line 147: verify ONLY the ordered book was removed
        // Cart should have 1 item remaining (libro2)
        assertEquals(1, carrello.getRigheCarrello().size(), 
                "Cart should have 1 item remaining (kills line 147 loop boundary mutation)");
        assertEquals(libro2, carrello.getRigheCarrello().get(0).getLibro(), 
                "Remaining item should be libro2");
        
        // Verify the correct book was deleted from DAO
        verify(rigaCarrelloDAO).deleteRigaCarrello(eq("BOOK1"), eq("CART1"));
        verify(rigaCarrelloDAO, never()).deleteRigaCarrello(eq("BOOK2"), anyString());
        
        verify(response).sendRedirect("index.html");
    }
}