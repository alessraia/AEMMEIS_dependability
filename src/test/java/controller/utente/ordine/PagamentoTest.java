package controller.utente.ordine;

import controller.utente.ordine.Pagamento;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.*;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.libroService.Sede;
import model.libroService.SedeDAO;
import model.ordineService.Ordine;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class PagamentoTest {

    private Pagamento servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private SedeDAO sedeDAO;

    @BeforeEach
    void setUp() {
        servletUnderTest = new Pagamento();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        sedeDAO = mock(SedeDAO.class);
        
        servletUnderTest.setSedeDAO(sedeDAO);
        when(sedeDAO.doRetrieveById(anyInt())).thenReturn(new Sede());
        when(request.getSession()).thenReturn(session);
    }


    /**
     * Flusso principale: inserimento indirizzo corretto -> pagamentoOrdine.jsp
     */
    @Test
    void testDoGet_AddressForm_Success() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        // Righe disponibili
        List<RigaCarrello> righe = new ArrayList<RigaCarrello>();
        Libro libro = new Libro();
        libro.setPrezzo(10.0);
        libro.setSconto(0);
        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setLibro(libro);
        rigaCarrello.setQuantita(2);
        rigaCarrello.setIdCarrello("2");
        righe.add(rigaCarrello);  // TOT = 20
        when(session.getAttribute("righeDisponibili")).thenReturn(righe);

        // Parametri di indirizzo
        when(request.getParameter("typeForm")).thenReturn("indirizzo");
        when(request.getParameter("indirizzo")).thenReturn("Via Roma");
        when(request.getParameter("cap")).thenReturn("80100");
        when(request.getParameter("citta")).thenReturn("Napoli");

        when(request.getRequestDispatcher("/WEB-INF/results/pagamentoOrdine.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        // Capture the ordine object to verify it was set correctly
        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);
        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        
        Ordine ordine = ordineCaptor.getValue();
        assertNotNull(ordine, "Ordine should be set as request attribute");
        assertEquals(20.0, ordine.getCosto(), 0.01, "Cost should be calculated correctly");
        assertEquals("Napoli", ordine.getCitta(), "City should be set correctly");
        assertEquals("Via Roma, 80100", ordine.getIndirizzoSpedizione(), "Address should be set correctly");
        
        verify(dispatcher).forward(request, response);
    }

    /**
     * Flusso alternativo: errore nell'indirizzo
     * UC_RF_GO_4.1 scenario 9.a -> campi non validi
     */
    @Test
    void testDoGet_AddressForm_Error() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        when(session.getAttribute("righeDisponibili")).thenReturn(new ArrayList<>());

        when(request.getParameter("typeForm")).thenReturn("indirizzo");
        when(request.getParameter("indirizzo")).thenReturn("");  // errore
        when(request.getParameter("cap")).thenReturn("abc");     // errore
        when(request.getParameter("citta")).thenReturn("");

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }

    /**
     * Flusso principale: inserimento sede -> pagamentoOrdine.jsp
     */
    @Test
    void testDoGet_SedeForm_Success() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        when(session.getAttribute("righeDisponibili")).thenReturn(new ArrayList<>());

        when(request.getParameter("typeForm")).thenReturn("sede");
        when(request.getParameter("sede")).thenReturn("1");
        
        // Mock sede object with specific values
        Sede sede = new Sede();
        sede.setCitta("Milano");
        sede.setVia("Via Garibaldi");
        sede.setCivico(10);
        sede.setCap("20100");
        when(sedeDAO.doRetrieveById(1)).thenReturn(sede);

        when(request.getRequestDispatcher("/WEB-INF/results/pagamentoOrdine.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        // Capture the ordine object to verify it was set correctly
        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);
        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        
        Ordine ordine = ordineCaptor.getValue();
        assertNotNull(ordine, "Ordine should be set as request attribute");
        assertEquals("Milano", ordine.getCitta(), "City should be set from sede");
        assertEquals("Via Garibaldi, 10, 20100", ordine.getIndirizzoSpedizione(), "Address should be set from sede");
        
        verify(dispatcher).forward(request, response);
    }

    /**
     * Flusso alternativo: sede non specificata -> errore
     */
    @Test
    void testDoGet_SedeForm_Error() throws ServletException, IOException {
        Utente user = new Utente();
        List<RigaCarrello> righeDisponibili = new ArrayList<RigaCarrello>();
        Libro libro = new Libro();
        libro.setDisponibile(true);
        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setLibro(libro);
        rigaCarrello.setIdCarrello("1");
        righeDisponibili.add(rigaCarrello);

        when(session.getAttribute("righeDisponibili")).thenReturn(righeDisponibili);
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        when(request.getParameter("typeForm")).thenReturn("sede");
        when(request.getParameter("sede")).thenReturn(""); // vuoto => errore

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }
    
    /**
     * Test to verify that cap=null is handled correctly (kills isNumeric mutation)
     */
    @Test
    void testDoGet_AddressForm_NullCap() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        when(session.getAttribute("righeDisponibili")).thenReturn(new ArrayList<>());

        when(request.getParameter("typeForm")).thenReturn("indirizzo");
        when(request.getParameter("indirizzo")).thenReturn("Via Roma");
        when(request.getParameter("cap")).thenReturn(null); // null cap
        when(request.getParameter("citta")).thenReturn("Napoli");

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }
    
    /**
     * Test to verify that non-numeric cap is rejected (kills isNumeric boolean return mutation)
     * Uses exactly 5 characters so only the isNumeric check fails
     */
    @Test
    void testDoGet_AddressForm_NonNumericCap() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        List<RigaCarrello> righe = new ArrayList<>();
        Libro libro = new Libro();
        libro.setPrezzo(10.0);
        libro.setSconto(0);
        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setLibro(libro);
        rigaCarrello.setQuantita(1);
        righe.add(rigaCarrello);
        when(session.getAttribute("righeDisponibili")).thenReturn(righe);

        when(request.getParameter("typeForm")).thenReturn("indirizzo");
        when(request.getParameter("indirizzo")).thenReturn("Via Roma");
        when(request.getParameter("cap")).thenReturn("AB123"); // 5 chars, but contains letters
        when(request.getParameter("citta")).thenReturn("Napoli");

        // Should go to ERROR page
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);
        // But if mutation survives (isNumeric always returns true), would go to success page
        RequestDispatcher successDispatcher = mock(RequestDispatcher.class);
        when(request.getRequestDispatcher("/WEB-INF/results/pagamentoOrdine.jsp"))
                .thenReturn(successDispatcher);

        servletUnderTest.doGet(request, response);

        // Must go to error page (not success page)
        verify(dispatcher).forward(request, response);
        verify(successDispatcher, never()).forward(request, response);
    }
    
    /**
     * Test with discount to verify price calculation mutations
     */
    @Test
    void testDoGet_WithDiscount() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        // Book with discount
        List<RigaCarrello> righe = new ArrayList<RigaCarrello>();
        Libro libro = new Libro();
        libro.setPrezzo(100.0);
        libro.setSconto(10); // 10% discount
        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setLibro(libro);
        rigaCarrello.setQuantita(2);
        righe.add(rigaCarrello);
        when(session.getAttribute("righeDisponibili")).thenReturn(righe);

        when(request.getParameter("typeForm")).thenReturn("indirizzo");
        when(request.getParameter("indirizzo")).thenReturn("Via Test");
        when(request.getParameter("cap")).thenReturn("12345");
        when(request.getParameter("citta")).thenReturn("TestCity");

        when(request.getRequestDispatcher("/WEB-INF/results/pagamentoOrdine.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        // Verify cost calculation: 100 - (100 * 10 / 100) = 90 per unit, 90 * 2 = 180
        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);
        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        
        Ordine ordine = ordineCaptor.getValue();
        assertEquals(180.0, ordine.getCosto(), 0.01, "Cost with discount should be calculated correctly");
    }
}