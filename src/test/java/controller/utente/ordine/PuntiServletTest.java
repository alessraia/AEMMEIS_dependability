package controller.utente.ordine;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.ordineService.Ordine;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;

import java.io.IOException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.*;

class PuntiServletTest {
    private PuntiServlet servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private Utente utente;

    @BeforeEach
    void setUp() {
        servletUnderTest = new PuntiServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        utente = mock(Utente.class);
        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utente);
        // Imposto valore di default per getTipo per evitare NPE nei test
        when(utente.getTipo()).thenReturn("");
        when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
    }

    @Test
    void testDoGet_UserIsAdmin() throws ServletException, IOException {
        // Simulo utente admin (Validator controlla che getTipo() inizi con "Gestore")
        when(utente.getTipo()).thenReturn("Gestore");
        servletUnderTest.doGet(request, response);
        verify(request).getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_UserIsNotAdmin() throws ServletException, IOException {
        when(utente.getTipo()).thenReturn("user");
        when(request.getParameter("citta")).thenReturn("Roma");
        when(request.getParameter("indirizzo")).thenReturn("Via Test");
        when(request.getParameter("punti")).thenReturn("10");
        when(request.getParameter("costo")).thenReturn("100.0");
        
        // ArgumentCaptor per verificare lo stato dell'oggetto Ordine
        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);
        
        servletUnderTest.doGet(request, response);
        
        verify(request).getRequestDispatcher("/WEB-INF/results/pagamentoOrdine.jsp");
        verify(dispatcher).forward(request, response);
        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        verify(request).setAttribute(eq("costo"), any());
        
        // Verifica che i setter siano stati chiamati e i valori impostati correttamente
        Ordine capturedOrdine = ordineCaptor.getValue();
        assertEquals("Roma", capturedOrdine.getCitta());
        assertEquals("Via Test", capturedOrdine.getIndirizzoSpedizione());
        assertEquals(10, capturedOrdine.getPuntiSpesi());
        // Verifica calcolo: 100.0 - (10 * 0.10) = 100.0 - 1.0 = 99.0
        assertEquals(99.0, capturedOrdine.getCosto(), 0.01);
    }
    
    @Test
    void testDoGet_WithNullPoints() throws ServletException, IOException {
        when(utente.getTipo()).thenReturn("user");
        when(request.getParameter("citta")).thenReturn("Milano");
        when(request.getParameter("indirizzo")).thenReturn("Via Roma 10");
        when(request.getParameter("punti")).thenReturn(null);
        when(request.getParameter("costo")).thenReturn("50.0");
        
        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);
        
        servletUnderTest.doGet(request, response);
        
        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        
        Ordine capturedOrdine = ordineCaptor.getValue();
        assertEquals("Milano", capturedOrdine.getCitta());
        assertEquals("Via Roma 10", capturedOrdine.getIndirizzoSpedizione());
        assertEquals(0, capturedOrdine.getPuntiSpesi());
        // Verifica calcolo: 50.0 - (0 * 0.10) = 50.0
        assertEquals(50.0, capturedOrdine.getCosto(), 0.01);
    }
    
    @Test
    void testDoGet_WithEmptyPoints() throws ServletException, IOException {
        when(utente.getTipo()).thenReturn("user");
        when(request.getParameter("citta")).thenReturn("Napoli");
        when(request.getParameter("indirizzo")).thenReturn("Via Garibaldi 5");
        when(request.getParameter("punti")).thenReturn("");
        when(request.getParameter("costo")).thenReturn("75.50");
        
        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);
        
        servletUnderTest.doGet(request, response);
        
        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        
        Ordine capturedOrdine = ordineCaptor.getValue();
        assertEquals("Napoli", capturedOrdine.getCitta());
        assertEquals("Via Garibaldi 5", capturedOrdine.getIndirizzoSpedizione());
        assertEquals(0, capturedOrdine.getPuntiSpesi());
        // Verifica calcolo: 75.50 - (0 * 0.10) = 75.50
        assertEquals(75.50, capturedOrdine.getCosto(), 0.01);
    }
    
    @Test
    void testDoGet_WithValidPointsCalculation() throws ServletException, IOException {
        when(utente.getTipo()).thenReturn("Premium");
        when(request.getParameter("citta")).thenReturn("Torino");
        when(request.getParameter("indirizzo")).thenReturn("Corso Italia 20");
        when(request.getParameter("punti")).thenReturn("50");
        when(request.getParameter("costo")).thenReturn("200.0");
        
        ArgumentCaptor<Ordine> ordineCaptor = ArgumentCaptor.forClass(Ordine.class);
        
        servletUnderTest.doGet(request, response);
        
        verify(request).setAttribute(eq("ordine"), ordineCaptor.capture());
        
        Ordine capturedOrdine = ordineCaptor.getValue();
        assertEquals("Torino", capturedOrdine.getCitta());
        assertEquals("Corso Italia 20", capturedOrdine.getIndirizzoSpedizione());
        assertEquals(50, capturedOrdine.getPuntiSpesi());
        // Verifica calcolo: 200.0 - (50 * 0.10) = 200.0 - 5.0 = 195.0
        assertEquals(195.0, capturedOrdine.getCosto(), 0.01);
    }
}
